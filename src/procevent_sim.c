/**
 * collectd - src/procevent.c
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *
 * Authors:
 *   Red Hat NFVPE
 *     Andrew Bays <abays at redhat.com>
 **/

#include "collectd.h"

#include "common.h"
#include "plugin.h"
#include "utils_complain.h"
#include "utils_ignorelist.h"

#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#include <dirent.h>
#include <linux/cn_proc.h>
#include <linux/connector.h>
#include <linux/netlink.h>
#include <linux/rtnetlink.h>
#include <signal.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define PROCEVENT_EXITED 0
#define PROCEVENT_STARTED 1
#define PROCEVENT_FIELDS 4 // pid, status, extra, timestamp
#define BUFSIZE 512
#define PROCDIR "/proc"

#define PROCEVENT_DOMAIN_FIELD "domain"
#define PROCEVENT_DOMAIN_VALUE "fault"
#define PROCEVENT_EVENT_ID_FIELD "eventId"
#define PROCEVENT_EVENT_NAME_FIELD "eventName"
#define PROCEVENT_EVENT_NAME_DOWN_VALUE "down"
#define PROCEVENT_EVENT_NAME_UP_VALUE "up"
#define PROCEVENT_LAST_EPOCH_MICROSEC_FIELD "lastEpochMicrosec"
#define PROCEVENT_PRIORITY_FIELD "priority"
#define PROCEVENT_PRIORITY_VALUE "high"
#define PROCEVENT_REPORTING_ENTITY_NAME_FIELD "reportingEntityName"
#define PROCEVENT_REPORTING_ENTITY_NAME_VALUE "collectd procevent plugin"
#define PROCEVENT_SEQUENCE_FIELD "sequence"
#define PROCEVENT_SEQUENCE_VALUE 0
#define PROCEVENT_SOURCE_NAME_FIELD "sourceName"
#define PROCEVENT_START_EPOCH_MICROSEC_FIELD "startEpochMicrosec"
#define PROCEVENT_VERSION_FIELD "version"
#define PROCEVENT_VERSION_VALUE 1.0

#define PROCEVENT_ALARM_CONDITION_FIELD "alarmCondition"
#define PROCEVENT_ALARM_INTERFACE_A_FIELD "alarmInterfaceA"
#define PROCEVENT_EVENT_SEVERITY_FIELD "eventSeverity"
#define PROCEVENT_EVENT_SEVERITY_CRITICAL_VALUE "CRITICAL"
#define PROCEVENT_EVENT_SEVERITY_NORMAL_VALUE "NORMAL"
#define PROCEVENT_EVENT_SOURCE_TYPE_FIELD "eventSourceType"
#define PROCEVENT_EVENT_SOURCE_TYPE_VALUE "process"
#define PROCEVENT_FAULT_FIELDS_FIELD "faultFields"
#define PROCEVENT_FAULT_FIELDS_VERSION_FIELD "faultFieldsVersion"
#define PROCEVENT_FAULT_FIELDS_VERSION_VALUE 1.0
#define PROCEVENT_SPECIFIC_PROBLEM_FIELD "specificProblem"
#define PROCEVENT_SPECIFIC_PROBLEM_DOWN_VALUE "down"
#define PROCEVENT_SPECIFIC_PROBLEM_UP_VALUE "up"
#define PROCEVENT_VF_STATUS_FIELD "vfStatus"
#define PROCEVENT_VF_STATUS_CRITICAL_VALUE "Ready to terminate"
#define PROCEVENT_VF_STATUS_NORMAL_VALUE "Active"

/*
 * Private data types
 */

typedef struct {
  int head;
  int tail;
  int maxLen;
  long long unsigned int **buffer;
} circbuf_t;

struct processlist_s {
  char *process;

  uint32_t pid;

  struct processlist_s *next;
};
typedef struct processlist_s processlist_t;

/*
 * Private variables
 */
static ignorelist_t *ignorelist = NULL;

static int procevent_thread_loop = 0;
static int procevent_thread_error = 0;
static pthread_t procevent_thread_id;
static pthread_mutex_t procevent_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t procevent_cond = PTHREAD_COND_INITIALIZER;
static int buffer_length;
static int chance = 2;
static int chance_total = 100000;
static int process_count = 0;
static circbuf_t ring;
static processlist_t *processlist_head = NULL;
static int event_id = 0;
static const char *process_names[] = {"ovs-vswitchd", "qemu-kvm", "nova-compute", "tuned", "libvirtd", "dockerd", "dnsmasq", "firewalld"};

static const char *config_keys[] = {"BufferLength", "Process", "ChanceTotal", "Chance"};
static int config_keys_num = STATIC_ARRAY_SIZE(config_keys);

/*
 * Private functions
 */

static int gen_metadata_payload(int state, int pid, const char *process,
                                long long unsigned int timestamp,
                                notification_t *n) {
  char tmp_str[DATA_MAX_NAME_LEN];
  notification_meta_t *header = NULL;
  notification_meta_t *domain = NULL;

  // *** BEGIN common event header ***

  // Add the object as "ves" to the notification's meta (the notification's meta
  // will be created by this call, and it will be the VES header)

  if (plugin_notification_meta_add_nested(n, "ves") != 0)
    goto err;

  // Now populate the VES header, but first we need to acquire it
  if (plugin_notification_meta_get_meta_tail(n, &header) != 0)
    goto err;

  if (header == NULL) {
    ERROR(
        "procevent_sim plugin: gen_metadata_payload could not acquire VES header.");
    goto err;
  }

  // domain
  if (plugin_notification_meta_append_string(header, PROCEVENT_DOMAIN_FIELD,
                                             PROCEVENT_DOMAIN_VALUE) != 0)
    goto err;

  // eventId
  event_id = event_id + 1;

  if (plugin_notification_meta_append_unsigned_int(
          header, PROCEVENT_EVENT_ID_FIELD, event_id) != 0)
    goto err;

  // eventName
  int event_name_len = 0;
  event_name_len = event_name_len + (sizeof(char) * sizeof(int) * 4); // pid
  event_name_len = event_name_len + strlen(process);      // process name
  event_name_len = event_name_len + (state == 0 ? 4 : 2); // "down" or "up"
  event_name_len = event_name_len +
                   13; // "process", 3 spaces, 2 parentheses and null-terminator
  memset(tmp_str, '\0', DATA_MAX_NAME_LEN);
  snprintf(tmp_str, event_name_len, "process %s (%d) %s", process, pid,
           (state == 0 ? PROCEVENT_EVENT_NAME_DOWN_VALUE
                       : PROCEVENT_EVENT_NAME_UP_VALUE));

  if (plugin_notification_meta_append_string(header, PROCEVENT_EVENT_NAME_FIELD,
                                             tmp_str) != 0)
    goto err;

  // lastEpochMicrosec
  if (plugin_notification_meta_append_unsigned_int(
          header, PROCEVENT_LAST_EPOCH_MICROSEC_FIELD,
          (long long unsigned int)CDTIME_T_TO_US(cdtime())) != 0)
    goto err;

  // priority
  if (plugin_notification_meta_append_string(header, PROCEVENT_PRIORITY_FIELD,
                                             PROCEVENT_PRIORITY_VALUE) != 0)
    goto err;

  // reportingEntityName
  if (plugin_notification_meta_append_string(
          header, PROCEVENT_REPORTING_ENTITY_NAME_FIELD,
          PROCEVENT_REPORTING_ENTITY_NAME_VALUE) != 0)

    // sequence
    if (plugin_notification_meta_append_unsigned_int(
            header, PROCEVENT_SEQUENCE_FIELD,
            (unsigned int)PROCEVENT_SEQUENCE_VALUE) != 0)
      goto err;

  // sourceName
  if (plugin_notification_meta_append_string(
          header, PROCEVENT_SOURCE_NAME_FIELD, process) != 0)

    // startEpochMicrosec
    if (plugin_notification_meta_append_unsigned_int(
            header, PROCEVENT_START_EPOCH_MICROSEC_FIELD,
            (long long unsigned int)timestamp) != 0)
      goto err;

  // version
  if (plugin_notification_meta_append_double(header, PROCEVENT_VERSION_FIELD,
                                             PROCEVENT_VERSION_VALUE) != 0)
    goto err;

  // *** END common event header ***

  // *** BEGIN fault fields ***

  // Append a nested metadata object to header, with key as "faultFields",
  // and then find it.  We will then append children data to it.

  if (plugin_notification_meta_append_nested(header,
                                             PROCEVENT_FAULT_FIELDS_FIELD) != 0)
    goto err;

  if (plugin_notification_meta_get_nested_tail(header, &domain) != 0)
    goto err;

  if (domain == NULL) {
    ERROR(
        "procevent_sim plugin: gen_metadata_payload could not acquire VES domain.");
    goto err;
  }

  // alarmCondition
  int alarm_condition_len = 0;
  alarm_condition_len =
      alarm_condition_len + (sizeof(char) * sizeof(int) * 4);  // pid
  alarm_condition_len = alarm_condition_len + strlen(process); // process name
  alarm_condition_len =
      alarm_condition_len + 25; // "process", "state", "change", 4 spaces, 2
                                // parentheses and null-terminator
  memset(tmp_str, '\0', DATA_MAX_NAME_LEN);
  snprintf(tmp_str, alarm_condition_len, "process %s (%d) state change",
           process, pid);

  if (plugin_notification_meta_append_string(
          domain, PROCEVENT_ALARM_CONDITION_FIELD, tmp_str) != 0)
    goto err;

  // alarmInterfaceA
  if (plugin_notification_meta_append_string(
          domain, PROCEVENT_ALARM_INTERFACE_A_FIELD, process) != 0)
    goto err;

  // eventSeverity
  if (plugin_notification_meta_append_string(
          domain, PROCEVENT_EVENT_SEVERITY_FIELD,
          (state == 0 ? PROCEVENT_EVENT_SEVERITY_CRITICAL_VALUE
                      : PROCEVENT_EVENT_SEVERITY_NORMAL_VALUE)) != 0)
    goto err;

  // eventSourceType
  if (plugin_notification_meta_append_string(
          domain, PROCEVENT_EVENT_SOURCE_TYPE_FIELD,
          PROCEVENT_EVENT_SOURCE_TYPE_VALUE) != 0)
    goto err;

  // faultFieldsVersion
  if (plugin_notification_meta_append_double(
          domain, PROCEVENT_FAULT_FIELDS_VERSION_FIELD,
          PROCEVENT_FAULT_FIELDS_VERSION_VALUE) != 0)
    goto err;

  // specificProblem
  int specific_problem_len = 0;
  specific_problem_len =
      specific_problem_len + (sizeof(char) * sizeof(int) * 4);   // pid
  specific_problem_len = specific_problem_len + strlen(process); // process name
  specific_problem_len =
      specific_problem_len + (state == 0 ? 4 : 2); // "down" or "up"
  specific_problem_len =
      specific_problem_len +
      13; // "process", 3 spaces, 2 parentheses and null-terminator
  memset(tmp_str, '\0', DATA_MAX_NAME_LEN);
  snprintf(tmp_str, specific_problem_len, "process %s (%d) %s", process, pid,
           (state == 0 ? PROCEVENT_SPECIFIC_PROBLEM_DOWN_VALUE
                       : PROCEVENT_SPECIFIC_PROBLEM_UP_VALUE));

  if (plugin_notification_meta_append_string(
          domain, PROCEVENT_SPECIFIC_PROBLEM_FIELD, tmp_str) != 0)
    goto err;

  // vfStatus
  if (plugin_notification_meta_append_string(
          domain, PROCEVENT_VF_STATUS_FIELD,
          (state == 0 ? PROCEVENT_VF_STATUS_CRITICAL_VALUE
                      : PROCEVENT_VF_STATUS_NORMAL_VALUE)) != 0)
    goto err;

  // *** END fault fields ***

  return 0;

err:
  ERROR("procevent_sim plugin: gen_metadata_payload failed to generate metadata");
  return -1;
}

// Does /proc/<pid>/comm contain a process name we are interested in?
// static processlist_t *process_check(int pid) {
//   int len, is_match, retval;
//   char file[BUFSIZE];
//   FILE *fh;
//   char buffer[BUFSIZE];

//   len = snprintf(file, sizeof(file), PROCDIR "/%d/comm", pid);

//   if ((len < 0) || (len >= BUFSIZE)) {
//     WARNING("procevent_sim process_check: process name too large");
//     return NULL;
//   }

//   if (NULL == (fh = fopen(file, "r"))) {
//     // No /proc/<pid>/comm for this pid, just ignore
//     DEBUG("procevent_sim plugin: no comm file available for pid %d", pid);
//     return NULL;
//   }

//   retval = fscanf(fh, "%[^\n]", buffer);

//   if (retval < 0) {
//     WARNING("procevent_sim process_check: unable to read comm file for pid %d",
//             pid);
//     fclose(fh);
//     return NULL;
//   }

//   // Now that we have the process name in the buffer, check if we are
//   // even interested in it
//   if (ignorelist_match(ignorelist, buffer) != 0) {
//     DEBUG("procevent_sim process_check: ignoring process %s (%d)", buffer, pid);
//     fclose(fh);
//     return NULL;
//   }

//   if (fh != NULL) {
//     fclose(fh);
//     fh = NULL;
//   }

//   //
//   // Go through the processlist linked list and look for the process name
//   // in /proc/<pid>/comm.  If found:
//   // 1. If pl->pid is -1, then set pl->pid to <pid> (and return that object)
//   // 2. If pl->pid is not -1, then another <process name> process was already
//   //    found.  If <pid> == pl->pid, this is an old match, so do nothing.
//   //    If the <pid> is different, however, make a new processlist_t and
//   //    associate <pid> with it (with the same process name as the existing).
//   //

//   pthread_mutex_lock(&procevent_list_lock);

//   processlist_t *pl;
//   processlist_t *match = NULL;

//   for (pl = processlist_head; pl != NULL; pl = pl->next) {

//     is_match = (strcmp(buffer, pl->process) == 0 ? 1 : 0);

//     if (is_match == 1) {
//       DEBUG("procevent_sim plugin: process %d name match for %s", pid, buffer);

//       if (pl->pid == pid) {
//         // this is a match, and we've already stored the exact pid/name combo
//         match = pl;
//         break;
//       } else if (pl->pid == -1) {
//         // this is a match, and we've found a candidate processlist_t to store
//         // this new pid/name combo
//         pl->pid = pid;
//         match = pl;
//         break;
//       } else if (pl->pid != -1) {
//         // this is a match, but another instance of this process has already
//         // claimed this pid/name combo,
//         // so keep looking
//         match = pl;
//         continue;
//       }
//     }
//   }

//   if (match == NULL ||
//       (match != NULL && match->pid != -1 && match->pid != pid)) {
//     // if there wasn't an existing match, OR
//     // if there was a match but the associated processlist_t object already
//     // contained a pid/name combo,
//     // then make a new one and add it to the linked list

//     DEBUG(
//         "procevent_sim plugin: allocating new processlist_t object for PID %d (%s)",
//         pid, buffer);

//     processlist_t *pl2;
//     char *process;

//     pl2 = malloc(sizeof(*pl2));
//     if (pl2 == NULL) {
//       char errbuf[1024];
//       ERROR("procevent_sim plugin: malloc failed during process_check: %s",
//             sstrerror(errno, errbuf, sizeof(errbuf)));
//       pthread_mutex_unlock(&procevent_list_lock);
//       return NULL;
//     }

//     process = strdup(buffer);
//     if (process == NULL) {
//       char errbuf[1024];
//       sfree(pl2);
//       ERROR("procevent_sim plugin: strdup failed during process_check: %s",
//             sstrerror(errno, errbuf, sizeof(errbuf)));
//       pthread_mutex_unlock(&procevent_list_lock);
//       return NULL;
//     }

//     pl2->process = process;
//     pl2->pid = pid;
//     pl2->next = processlist_head;
//     processlist_head = pl2;

//     match = pl2;
//   }

//   pthread_mutex_unlock(&procevent_list_lock);

//   return match;
// }

// Does our map have this PID or name?
// static processlist_t *process_map_check(int pid, char *process) {
//   processlist_t *pl;

//   pthread_mutex_lock(&procevent_list_lock);

//   for (pl = processlist_head; pl != NULL; pl = pl->next) {
//     int match_pid = 0;
//     int match_process = 0;
//     int match = 0;

//     if (pid > 0) {
//       if (pl->pid == pid)
//         match_pid = 1;
//     }

//     if (process != NULL) {
//       if (strcmp(pl->process, process) == 0)
//         match_process = 1;
//     }

//     if (pid > 0 && process == NULL && match_pid == 1)
//       match = 1;
//     else if (pid < 0 && process != NULL && match_process == 1)
//       match = 1;
//     else if (pid > 0 && process != NULL && match_pid == 1 && match_process == 1)
//       match = 1;

//     if (match == 1) {
//       pthread_mutex_unlock(&procevent_list_lock);
//       return pl;
//     }
//   }

//   pthread_mutex_unlock(&procevent_list_lock);

//   return NULL;
// }

// static int process_map_refresh(void) {
//   DIR *proc;

//   errno = 0;
//   proc = opendir(PROCDIR);
//   if (proc == NULL) {
//     char errbuf[1024];
//     ERROR("procevent_sim plugin: fopen (%s): %s", PROCDIR,
//           sstrerror(errno, errbuf, sizeof(errbuf)));
//     return -1;
//   }

//   while (42) {
//     struct dirent *dent;
//     int len;
//     char file[BUFSIZE];

//     struct stat statbuf;

//     int status;

//     errno = 0;
//     dent = readdir(proc);
//     if (dent == NULL) {
//       char errbuf[4096];

//       if (errno == 0) /* end of directory */
//         break;

//       ERROR("procevent_sim plugin: failed to read directory %s: %s", PROCDIR,
//             sstrerror(errno, errbuf, sizeof(errbuf)));
//       closedir(proc);
//       return -1;
//     }

//     if (dent->d_name[0] == '.')
//       continue;

//     len = snprintf(file, sizeof(file), PROCDIR "/%s", dent->d_name);
//     if ((len < 0) || (len >= BUFSIZE))
//       continue;

//     status = stat(file, &statbuf);
//     if (status != 0) {
//       char errbuf[4096];
//       WARNING("procevent_sim plugin: stat (%s) failed: %s", file,
//               sstrerror(errno, errbuf, sizeof(errbuf)));
//       continue;
//     }

//     if (!S_ISDIR(statbuf.st_mode))
//       continue;

//     len = snprintf(file, sizeof(file), PROCDIR "/%s/comm", dent->d_name);
//     if ((len < 0) || (len >= BUFSIZE))
//       continue;

//     int not_number = 0;

//     for (int i = 0; i < strlen(dent->d_name); i++) {
//       if (!isdigit(dent->d_name[i])) {
//         not_number = 1;
//         break;
//       }
//     }

//     if (not_number != 0)
//       continue;

//     // Check if we need to store this pid/name combo in our processlist_t linked
//     // list
//     int this_pid = atoi(dent->d_name);
//     processlist_t *pl = process_check(this_pid);

//     if (pl != NULL)
//       DEBUG("procevent_sim plugin: process map refreshed for PID %d and name %s",
//             this_pid, pl->process);
//   }

//   closedir(proc);

//   return 0;
// }

// static int nl_connect() {
//   int rc;
//   struct sockaddr_nl sa_nl;

//   nl_sock = socket(PF_NETLINK, SOCK_DGRAM, NETLINK_CONNECTOR);
//   if (nl_sock == -1) {
//     ERROR("procevent_sim plugin: socket open failed.");
//     return -1;
//   }

//   sa_nl.nl_family = AF_NETLINK;
//   sa_nl.nl_groups = CN_IDX_PROC;
//   sa_nl.nl_pid = getpid();

//   rc = bind(nl_sock, (struct sockaddr *)&sa_nl, sizeof(sa_nl));
//   if (rc == -1) {
//     ERROR("procevent_sim plugin: socket bind failed.");
//     close(nl_sock);
//     return -1;
//   }

//   return 0;
// }

// static int set_proc_ev_listen(bool enable) {
//   int rc;
//   struct __attribute__((aligned(NLMSG_ALIGNTO))) {
//     struct nlmsghdr nl_hdr;
//     struct __attribute__((__packed__)) {
//       struct cn_msg cn_msg;
//       enum proc_cn_mcast_op cn_mcast;
//     };
//   } nlcn_msg;

//   memset(&nlcn_msg, 0, sizeof(nlcn_msg));
//   nlcn_msg.nl_hdr.nlmsg_len = sizeof(nlcn_msg);
//   nlcn_msg.nl_hdr.nlmsg_pid = getpid();
//   nlcn_msg.nl_hdr.nlmsg_type = NLMSG_DONE;

//   nlcn_msg.cn_msg.id.idx = CN_IDX_PROC;
//   nlcn_msg.cn_msg.id.val = CN_VAL_PROC;
//   nlcn_msg.cn_msg.len = sizeof(enum proc_cn_mcast_op);

//   nlcn_msg.cn_mcast = enable ? PROC_CN_MCAST_LISTEN : PROC_CN_MCAST_IGNORE;

//   rc = send(nl_sock, &nlcn_msg, sizeof(nlcn_msg), 0);
//   if (rc == -1) {
//     ERROR("procevent_sim plugin: subscribing to netlink process events failed.");
//     return -1;
//   }

//   return 0;
// }

static int read_event() {
  int ret = 0;
  int proc_id = -1;
  int proc_status = -1;
  int proc_extra = -1;

  if (rand() % chance_total <= chance)
  {
    proc_id = (rand() % 300000) + 100;

    if ((int)(rand() % 2) == 0)
      proc_status = PROCEVENT_STARTED;
    else {
      proc_status = PROCEVENT_EXITED;
      proc_extra = -9;
    }
  }

  if (proc_status != -1) {
    pthread_mutex_lock(&procevent_lock);

    int next = ring.head + 1;
    if (next >= ring.maxLen)
      next = 0;

    if (next == ring.tail) {
      WARNING("procevent_sim plugin: ring buffer full");
    } else {
      DEBUG("procevent_sim plugin: Process %d status is now %s at %llu", proc_id,
            (proc_status == PROCEVENT_EXITED ? "EXITED" : "STARTED"),
            (long long unsigned int)CDTIME_T_TO_US(cdtime()));

      if (proc_status == PROCEVENT_EXITED) {
        ring.buffer[ring.head][0] = proc_id;
        ring.buffer[ring.head][1] = proc_status;
        ring.buffer[ring.head][2] = proc_extra;
        ring.buffer[ring.head][3] =
            (long long unsigned int)CDTIME_T_TO_US(cdtime());
      } else {
        ring.buffer[ring.head][0] = proc_id;
        ring.buffer[ring.head][1] = proc_status;
        ring.buffer[ring.head][2] = 0;
        ring.buffer[ring.head][3] =
            (long long unsigned int)CDTIME_T_TO_US(cdtime());
      }

      ring.head = next;
    }

    pthread_mutex_unlock(&procevent_lock);
  }

  return ret;
}

static void *procevent_thread(void *arg) /* {{{ */
{
  pthread_mutex_lock(&procevent_lock);

  while (procevent_thread_loop > 0) {
    int status;

    pthread_mutex_unlock(&procevent_lock);

    usleep(1000);

    status = read_event();

    pthread_mutex_lock(&procevent_lock);

    if (status < 0) {
      procevent_thread_error = 1;
      break;
    }

    if (procevent_thread_loop <= 0)
      break;
  } /* while (procevent_thread_loop > 0) */

  pthread_mutex_unlock(&procevent_lock);

  return ((void *)0);
} /* }}} void *procevent_thread */

static int start_thread(void) /* {{{ */
{
  int status;

  pthread_mutex_lock(&procevent_lock);

  if (procevent_thread_loop != 0) {
    pthread_mutex_unlock(&procevent_lock);
    return (0);
  }

  // if (nl_sock == -1) {
  //   status = nl_connect();

  //   if (status != 0)
  //     return status;

  //   status = set_proc_ev_listen(true);
  //   if (status == -1)
  //     return status;
  // }

  // DEBUG("procevent_sim plugin: socket created and bound");

  procevent_thread_loop = 1;
  procevent_thread_error = 0;

  status = plugin_thread_create(&procevent_thread_id, /* attr = */ NULL,
                                procevent_thread,
                                /* arg = */ (void *)0, "procevent_sim");
  if (status != 0) {
    procevent_thread_loop = 0;
    ERROR("procevent_sim plugin: Starting thread failed.");
    pthread_mutex_unlock(&procevent_lock);
    return (-1);
  }

  pthread_mutex_unlock(&procevent_lock);
  return (0);
} /* }}} int start_thread */

static int stop_thread(int shutdown) /* {{{ */
{
  int status;

  // if (nl_sock != -1) {
  //   status = close(nl_sock);
  //   if (status != 0) {
  //     ERROR("procevent_sim plugin: failed to close socket %d: %d (%s)", nl_sock,
  //           status, strerror(errno));
  //     return (-1);
  //   } else
  //     nl_sock = -1;
  // }

  pthread_mutex_lock(&procevent_lock);

  if (procevent_thread_loop == 0) {
    pthread_mutex_unlock(&procevent_lock);
    return (-1);
  }

  procevent_thread_loop = 0;
  pthread_cond_broadcast(&procevent_cond);
  pthread_mutex_unlock(&procevent_lock);

  if (shutdown == 1) {
    // Calling pthread_cancel here in
    // the case of a shutdown just assures that the thread is
    // gone and that the process has been fully terminated.

    DEBUG("procevent_sim plugin: Canceling thread for process shutdown");

    status = pthread_cancel(procevent_thread_id);

    if (status != 0) {
      ERROR("procevent_sim plugin: Unable to cancel thread: %d", status);
      status = -1;
    }
  } else {
    status = pthread_join(procevent_thread_id, /* return = */ NULL);
    if (status != 0) {
      ERROR("procevent_sim plugin: Stopping thread failed.");
      status = -1;
    }
  }

  pthread_mutex_lock(&procevent_lock);
  memset(&procevent_thread_id, 0, sizeof(procevent_thread_id));
  procevent_thread_error = 0;
  pthread_mutex_unlock(&procevent_lock);

  DEBUG("procevent_sim plugin: Finished requesting stop of thread");

  return (status);
} /* }}} int stop_thread */

static int procevent_init(void) /* {{{ */
{
  ring.head = 0;
  ring.tail = 0;
  ring.maxLen = buffer_length;
  ring.buffer = (long long unsigned int **)malloc(
      buffer_length * sizeof(long long unsigned int *));

  for (int i = 0; i < buffer_length; i++) {
    ring.buffer[i] = (long long unsigned int *)malloc(
        PROCEVENT_FIELDS * sizeof(long long unsigned int));
  }

  if (ignorelist == NULL || ignorelist->head == NULL) {
    NOTICE("procevent_sim plugin: No processes have been configured, canned names will be used");
  }

  srand(time(NULL));

  return (start_thread());
} /* }}} int procevent_init */

static int procevent_config(const char *key, const char *value) /* {{{ */
{
  if (ignorelist == NULL)
    ignorelist = ignorelist_create(/* invert = */ 1);

  if (strcasecmp(key, "BufferLength") == 0) {
    buffer_length = atoi(value);
  } else if (strcasecmp(key, "Process") == 0) {
    ignorelist_add(ignorelist, value);
    process_count ++;
  } else if (strcasecmp(key, "ChanceTotal") == 0) {
    chance_total = atoi(value);
  } else if (strcasecmp(key, "Chance") == 0) {
    chance = atoi(value);
  } else {
    return (-1);
  }

  return (0);
} /* }}} int procevent_config */

static void procevent_dispatch_notification(int pid, const char *type, /* {{{ */
                                            gauge_t value, const char *process,
                                            long long unsigned int timestamp) {

  notification_t n = {NOTIF_FAILURE, cdtime(), "", "", "procevent", "", "", "",
                      NULL};

  if (value == 1)
    n.severity = NOTIF_OKAY;

  sstrncpy(n.host, hostname_g, sizeof(n.host));
  sstrncpy(n.plugin_instance, process, sizeof(n.plugin_instance));
  sstrncpy(n.type, "gauge", sizeof(n.type));
  sstrncpy(n.type_instance, "process_status", sizeof(n.type_instance));

  gen_metadata_payload(value, pid, process, timestamp, &n);

  DEBUG("procevent_sim plugin: dispatching state %d for PID %d (%s)", (int)value,
        pid, process);

  plugin_dispatch_notification(&n);
  plugin_notification_meta_free(n.meta);
}

static void procevent_submit(int pid, const char *type, /* {{{ */
                   gauge_t value, const char *process) {
  value_list_t vl = VALUE_LIST_INIT;

  vl.values = &(value_t){.gauge = value};
  vl.values_len = 1;
  sstrncpy(vl.plugin, "procevent", sizeof(vl.plugin));
  sstrncpy(vl.plugin_instance, process, sizeof(vl.plugin_instance));
  sstrncpy(vl.type, type, sizeof(vl.type));

  DEBUG("procevent_sim plugin: dispatching state %d for PID %d (%s)", (int)value,
        pid, process);

  // Create metadata to store JSON key-values
  meta_data_t *meta = meta_data_create();

  vl.meta = meta;

  meta_data_add_string(meta, "entity", process);

  plugin_dispatch_values(&vl);

  meta_data_destroy(meta);
} /* }}} void interface_submit */

static int procevent_read(void) /* {{{ */
{
  if (procevent_thread_error != 0) {
    ERROR(
        "procevent_sim plugin: The interface thread had a problem. Restarting it.");

    stop_thread(0);

    start_thread();

    return (-1);
  } /* if (procevent_thread_error != 0) */

  pthread_mutex_lock(&procevent_lock);

  while (ring.head != ring.tail) {
    int next = ring.tail + 1;

    if (next >= ring.maxLen)
      next = 0;

    // Pick a random process name
    ignorelist_item_t *this;
    ignorelist_item_t *next_item;

    int stop = -1;
    int i = 0;
    const char * choice = NULL;

    if (ignorelist == NULL || ignorelist->head == NULL) {
      i = (int)(rand() % 8);
      choice = process_names[i];
    } else {
      stop = (int)(rand() % process_count);
      for (this = ignorelist->head; this != NULL; this = next_item) {
        if (i == stop)
        {
          choice = this->smatch;
          break;
        }
        next_item = this->next;
        i ++;
      }
    }

    if (ring.buffer[ring.tail][1] == PROCEVENT_EXITED) {
        procevent_dispatch_notification(ring.buffer[ring.tail][0], "gauge",
                                        ring.buffer[ring.tail][1], choice,
                                        ring.buffer[ring.tail][3]);
        DEBUG("procevent_sim plugin: PID %llu (%s) EXITED, removing PID from process "
              "list",
              ring.buffer[ring.tail][0], choice);
    } else if (ring.buffer[ring.tail][1] == PROCEVENT_STARTED) {
        // This process is of interest to us, so publish its STARTED status
        procevent_dispatch_notification(ring.buffer[ring.tail][0], "gauge",
                                        ring.buffer[ring.tail][1], choice,
                                        ring.buffer[ring.tail][3]);
        DEBUG(
            "procevent_sim plugin: PID %llu (%s) STARTED, adding PID to process list",
            ring.buffer[ring.tail][0], choice);
    }

    procevent_submit(ring.buffer[ring.tail][0], "gauge", ring.buffer[ring.tail][1], choice);

    ring.tail = next;
  }

  pthread_mutex_unlock(&procevent_lock);

  return (0);
} /* }}} int procevent_read */

static int procevent_shutdown(void) /* {{{ */
{
  processlist_t *pl;

  DEBUG("procevent_sim plugin: Shutting down thread.");

  if (stop_thread(1) < 0)
    return (-1);

  for (int i = 0; i < buffer_length; i++) {
    free(ring.buffer[i]);
  }

  free(ring.buffer);

  pl = processlist_head;
  while (pl != NULL) {
    processlist_t *pl_next;

    pl_next = pl->next;

    sfree(pl->process);
    sfree(pl);

    pl = pl_next;
  }

  return (0);
} /* }}} int procevent_shutdown */

void module_register(void) {
  plugin_register_config("procevent_sim", procevent_config, config_keys,
                         config_keys_num);
  plugin_register_init("procevent_sim", procevent_init);
  plugin_register_read("procevent_sim", procevent_read);
  plugin_register_shutdown("procevent_sim", procevent_shutdown);
} /* void module_register */

