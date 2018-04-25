/**
 * collectd - src/connectivity.c
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
 *     Aneesh Puttur <aputtur at redhat.com>
 **/

#include "collectd.h"

#include "common.h"
#include "plugin.h"
#include "utils_complain.h"
#include "utils_ignorelist.h"

#include <errno.h>
#include <net/if.h>
#include <netinet/in.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#include <libmnl/libmnl.h>
#include <linux/netlink.h>
#include <linux/rtnetlink.h>

#define MYPROTO NETLINK_ROUTE

#define LINK_STATE_DOWN 0
#define LINK_STATE_UP 1
#define LINK_STATE_UNKNOWN 2

#define CONNECTIVITY_DOMAIN_FIELD "domain"
#define CONNECTIVITY_DOMAIN_VALUE "stateChange"
#define CONNECTIVITY_EVENT_ID_FIELD "eventId"
#define CONNECTIVITY_EVENT_NAME_FIELD "eventName"
#define CONNECTIVITY_EVENT_NAME_DOWN_VALUE "down"
#define CONNECTIVITY_EVENT_NAME_UP_VALUE "up"
#define CONNECTIVITY_LAST_EPOCH_MICROSEC_FIELD "lastEpochMicrosec"
#define CONNECTIVITY_PRIORITY_FIELD "priority"
#define CONNECTIVITY_PRIORITY_VALUE "high"
#define CONNECTIVITY_REPORTING_ENTITY_NAME_FIELD "reportingEntityName"
#define CONNECTIVITY_REPORTING_ENTITY_NAME_VALUE "collectd connectivity plugin"
#define CONNECTIVITY_SEQUENCE_FIELD "sequence"
#define CONNECTIVITY_SEQUENCE_VALUE 0
#define CONNECTIVITY_SOURCE_NAME_FIELD "sourceName"
#define CONNECTIVITY_START_EPOCH_MICROSEC_FIELD "startEpochMicrosec"
#define CONNECTIVITY_VERSION_FIELD "version"
#define CONNECTIVITY_VERSION_VALUE 1.0

#define CONNECTIVITY_NEW_STATE_FIELD "newState"
#define CONNECTIVITY_NEW_STATE_FIELD_DOWN_VALUE "outOfService"
#define CONNECTIVITY_NEW_STATE_FIELD_UP_VALUE "inService"
#define CONNECTIVITY_OLD_STATE_FIELD "oldState"
#define CONNECTIVITY_OLD_STATE_FIELD_DOWN_VALUE "outOfService"
#define CONNECTIVITY_OLD_STATE_FIELD_UP_VALUE "inService"
#define CONNECTIVITY_STATE_CHANGE_FIELDS_FIELD "stateChangeFields"
#define CONNECTIVITY_STATE_CHANGE_FIELDS_VERSION_FIELD                         \
  "stateChangeFieldsVersion"
#define CONNECTIVITY_STATE_CHANGE_FIELDS_VERSION_VALUE 1.0
#define CONNECTIVITY_STATE_INTERFACE_FIELD "stateInterface"

/*
 * Private data types
 */
struct interface_list_s {
  char *interface;

  uint32_t status;
  uint32_t prev_status;
  uint32_t sent;
  long long unsigned int timestamp;

  struct interface_list_s *next;
};
typedef struct interface_list_s interface_list_t;

/*
 * Private variables
 */
static ignorelist_t *ignorelist = NULL;

static interface_list_t *interface_list_head = NULL;
static int monitor_all_interfaces = 1;

static int connectivity_thread_loop = 0;
static int connectivity_thread_error = 0;
static pthread_t connectivity_thread_id;
static pthread_mutex_t connectivity_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t connectivity_cond = PTHREAD_COND_INITIALIZER;
static struct mnl_socket *sock;
static unsigned int event_id = 0;
static int send_metrics = 0;

static const char *config_keys[] = {"Interface", "SendMetrics"};
static int config_keys_num = STATIC_ARRAY_SIZE(config_keys);

/*
 * Private functions
 */

static int gen_metadata_payload(int state, int old_state, const char *interface,
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
    ERROR("connectivity plugin: gen_metadata_payload could not acquire VES "
          "header.");
    goto err;
  }

  // domain
  if (plugin_notification_meta_append_string(header, CONNECTIVITY_DOMAIN_FIELD,
                                             CONNECTIVITY_DOMAIN_VALUE) != 0)
    goto err;

  // eventId
  event_id = event_id + 1;

  if (plugin_notification_meta_append_unsigned_int(
          header, CONNECTIVITY_EVENT_ID_FIELD, event_id) != 0)
    goto err;

  // eventName
  int event_name_len = 0;
  event_name_len = event_name_len + strlen(interface);    // interface name
  event_name_len = event_name_len + (state == 0 ? 4 : 2); // "down" or "up"
  event_name_len =
      event_name_len + 12; // "interface", 2 spaces and null-terminator
  memset(tmp_str, '\0', DATA_MAX_NAME_LEN);
  snprintf(tmp_str, event_name_len, "interface %s %s", interface,
           (state == 0 ? CONNECTIVITY_EVENT_NAME_DOWN_VALUE
                       : CONNECTIVITY_EVENT_NAME_UP_VALUE));

  if (plugin_notification_meta_append_string(
          header, CONNECTIVITY_EVENT_NAME_FIELD, tmp_str) != 0)
    goto err;

  // lastEpochMicrosec
  if (plugin_notification_meta_append_unsigned_int(
          header, CONNECTIVITY_LAST_EPOCH_MICROSEC_FIELD,
          (long long unsigned int)CDTIME_T_TO_US(cdtime())) != 0)
    goto err;

  // priority
  if (plugin_notification_meta_append_string(header,
                                             CONNECTIVITY_PRIORITY_FIELD,
                                             CONNECTIVITY_PRIORITY_VALUE) != 0)
    goto err;

  // reportingEntityName
  if (plugin_notification_meta_append_string(
          header, CONNECTIVITY_REPORTING_ENTITY_NAME_FIELD,
          CONNECTIVITY_REPORTING_ENTITY_NAME_VALUE) != 0)

    // sequence
    if (plugin_notification_meta_append_unsigned_int(
            header, CONNECTIVITY_SEQUENCE_FIELD,
            (unsigned int)CONNECTIVITY_SEQUENCE_VALUE) != 0)
      goto err;

  // sourceName
  if (plugin_notification_meta_append_string(
          header, CONNECTIVITY_SOURCE_NAME_FIELD, interface) != 0)

    // startEpochMicrosec
    if (plugin_notification_meta_append_unsigned_int(
            header, CONNECTIVITY_START_EPOCH_MICROSEC_FIELD,
            (long long unsigned int)timestamp) != 0)
      goto err;

  // version
  if (plugin_notification_meta_append_double(header, CONNECTIVITY_VERSION_FIELD,
                                             CONNECTIVITY_VERSION_VALUE) != 0)
    goto err;

  // *** END common event header ***

  // *** BEGIN state change fields ***

  // Append a nested metadata object to header, with key as "stateChangeFields",
  // and then find it.  We will then append children data to it.

  if (plugin_notification_meta_append_nested(
          header, CONNECTIVITY_STATE_CHANGE_FIELDS_FIELD) != 0)
    goto err;

  if (plugin_notification_meta_get_nested_tail(header, &domain) != 0)
    goto err;

  if (domain == NULL) {
    ERROR("connectivity plugin: gen_metadata_payload could not acquire VES "
          "domain.");
    goto err;
  }

  // newState
  if (plugin_notification_meta_append_string(
          domain, CONNECTIVITY_NEW_STATE_FIELD,
          (state == 0 ? CONNECTIVITY_NEW_STATE_FIELD_DOWN_VALUE
                      : CONNECTIVITY_NEW_STATE_FIELD_UP_VALUE)) != 0)
    goto err;

  // oldState
  if (plugin_notification_meta_append_string(
          domain, CONNECTIVITY_OLD_STATE_FIELD,
          (old_state == 0 ? CONNECTIVITY_OLD_STATE_FIELD_DOWN_VALUE
                          : CONNECTIVITY_OLD_STATE_FIELD_UP_VALUE)) != 0)
    goto err;

  // stateChangeFieldsVersion
  if (plugin_notification_meta_append_double(
          domain, CONNECTIVITY_STATE_CHANGE_FIELDS_VERSION_FIELD,
          CONNECTIVITY_STATE_CHANGE_FIELDS_VERSION_VALUE) != 0)
    goto err;

  // stateInterface
  if (plugin_notification_meta_append_string(
          domain, CONNECTIVITY_STATE_INTERFACE_FIELD, interface) != 0)
    goto err;

  // *** END state change fields ***

  return 0;

err:
  ERROR(
      "connectivity plugin: gen_metadata_payload failed to generate metadata");
  return -1;
}

static interface_list_t *add_interface(const char *interface, int status,
                                       int prev_status) {
  interface_list_t *il;
  char *interface2;

  il = malloc(sizeof(*il));
  if (il == NULL) {
    char errbuf[1024];
    ERROR("connectivity plugin: malloc failed during add_interface: %s",
          sstrerror(errno, errbuf, sizeof(errbuf)));
    return NULL;
  }

  interface2 = strdup(interface);
  if (interface2 == NULL) {
    char errbuf[1024];
    sfree(il);
    ERROR("connectivity plugin: strdup failed during add_interface: %s",
          sstrerror(errno, errbuf, sizeof(errbuf)));
    return NULL;
  }

  il->interface = interface2;
  il->status = status;
  il->prev_status = prev_status;
  il->timestamp = (long long unsigned int)CDTIME_T_TO_US(cdtime());
  il->sent = 0;
  il->next = interface_list_head;
  interface_list_head = il;

  DEBUG("connectivity plugin: added interface %s", interface2);

  return il;
}

static int connectivity_link_state(struct nlmsghdr *msg) {
  int retval = 0;
  struct ifinfomsg *ifi = mnl_nlmsg_get_payload(msg);
  struct nlattr *attr;
  const char *dev = NULL;

  pthread_mutex_lock(&connectivity_lock);

  interface_list_t *il = NULL;

  /* Scan attribute list for device name. */
  mnl_attr_for_each(attr, msg, sizeof(*ifi)) {
    if (mnl_attr_get_type(attr) != IFLA_IFNAME)
      continue;

    if (mnl_attr_validate(attr, MNL_TYPE_STRING) < 0) {
      ERROR("connectivity plugin: connectivity_link_state: IFLA_IFNAME "
            "mnl_attr_validate "
            "failed.");
      pthread_mutex_unlock(&connectivity_lock);
      return MNL_CB_ERROR;
    }

    dev = mnl_attr_get_str(attr);

    // Check the list of interfaces we should monitor, if we've chosen
    // a subset.  If we don't care about this one, abort.
    if (ignorelist_match(ignorelist, dev) != 0) {
      DEBUG("connectivity plugin: Ignoring link state change for unmonitored "
            "interface: %s",
            dev);
      break;
    }

    for (il = interface_list_head; il != NULL; il = il->next)
      if (strcmp(dev, il->interface) == 0)
        break;

    uint32_t prev_status;

    if (il == NULL) {
      // We haven't encountered this interface yet, so add it to the linked list
      il = add_interface(dev, LINK_STATE_UNKNOWN, LINK_STATE_UNKNOWN);

      if (il == NULL) {
        ERROR("connectivity plugin: unable to add interface %s during "
              "connectivity_link_state",
              dev);
        return MNL_CB_ERROR;
      }
    }

    prev_status = il->status;
    il->status =
        ((ifi->ifi_flags & IFF_RUNNING) ? LINK_STATE_UP : LINK_STATE_DOWN);
    il->timestamp = (long long unsigned int)CDTIME_T_TO_US(cdtime());

    // If the new status is different than the previous status,
    // store the previous status and set sent to zero
    if (il->status != prev_status) {
      il->prev_status = prev_status;
      il->sent = 0;
    }

    DEBUG("connectivity plugin (%llu): Interface %s status is now %s",
          il->timestamp, dev, ((ifi->ifi_flags & IFF_RUNNING) ? "UP" : "DOWN"));

    // no need to loop again, we found the interface name attr
    // (otherwise the first if-statement in the loop would
    // have moved us on with 'continue')
    break;
  }

  pthread_mutex_unlock(&connectivity_lock);

  return retval;
}

static int msg_handler(struct nlmsghdr *msg) {
  switch (msg->nlmsg_type) {
  case RTM_NEWADDR:
  case RTM_DELADDR:
  case RTM_NEWROUTE:
  case RTM_DELROUTE:
  case RTM_DELLINK:
    // Not of interest in current version
    break;
  case RTM_NEWLINK:
    connectivity_link_state(msg);
    break;
  default:
    ERROR("connectivity plugin: msg_handler: Unknown netlink nlmsg_type %d\n",
          msg->nlmsg_type);
    break;
  }
  return 0;
}

static int read_event(struct mnl_socket *nl,
                      int (*msg_handler)(struct nlmsghdr *)) {
  int status;
  int ret = 0;
  char buf[4096];
  struct nlmsghdr *h;

  if (nl == NULL)
    return ret;

  status = mnl_socket_recvfrom(nl, buf, sizeof(buf));

  if (status < 0) {
    /* Socket non-blocking so bail out once we have read everything */
    if (errno == EWOULDBLOCK || errno == EAGAIN)
      return ret;

    /* Anything else is an error */
    ERROR("connectivity plugin: read_event: Error mnl_socket_recvfrom: %d\n",
          status);
    return status;
  }

  if (status == 0) {
    DEBUG("connectivity plugin: read_event: EOF\n");
  }

  /* We need to handle more than one message per 'recvmsg' */
  for (h = (struct nlmsghdr *)buf; NLMSG_OK(h, (unsigned int)status);
       h = NLMSG_NEXT(h, status)) {
    /* Finish reading */
    if (h->nlmsg_type == NLMSG_DONE)
      return ret;

    /* Message is some kind of error */
    if (h->nlmsg_type == NLMSG_ERROR) {
      ERROR("connectivity plugin: read_event: Message is an error\n");
      return -1; // Error
    }

    /* Call message handler */
    if (msg_handler) {
      ret = (*msg_handler)(h);
      if (ret < 0) {
        ERROR("connectivity plugin: read_event: Message handler error %d\n",
              ret);
        return ret;
      }
    } else {
      ERROR("connectivity plugin: read_event: Error NULL message handler\n");
      return -1;
    }
  }

  return ret;
}

static void *connectivity_thread(void *arg) /* {{{ */
{
  pthread_mutex_lock(&connectivity_lock);

  while (connectivity_thread_loop > 0) {
    int status;

    pthread_mutex_unlock(&connectivity_lock);

    status = read_event(sock, msg_handler);

    pthread_mutex_lock(&connectivity_lock);

    if (status < 0) {
      connectivity_thread_error = 1;
      break;
    }

    if (connectivity_thread_loop <= 0)
      break;
  } /* while (connectivity_thread_loop > 0) */

  pthread_mutex_unlock(&connectivity_lock);

  return ((void *)0);
} /* }}} void *connectivity_thread */

static int start_thread(void) /* {{{ */
{
  int status;

  pthread_mutex_lock(&connectivity_lock);

  if (connectivity_thread_loop != 0) {
    pthread_mutex_unlock(&connectivity_lock);
    return (0);
  }

  connectivity_thread_loop = 1;
  connectivity_thread_error = 0;

  if (sock == NULL) {
    sock = mnl_socket_open(NETLINK_ROUTE);
    if (sock == NULL) {
      ERROR(
          "connectivity plugin: connectivity_thread: mnl_socket_open failed.");
      pthread_mutex_unlock(&connectivity_lock);
      return (-1);
    }

    if (mnl_socket_bind(sock, RTMGRP_LINK, MNL_SOCKET_AUTOPID) < 0) {
      ERROR(
          "connectivity plugin: connectivity_thread: mnl_socket_bind failed.");
      pthread_mutex_unlock(&connectivity_lock);
      return (1);
    }
  }

  status = plugin_thread_create(&connectivity_thread_id, /* attr = */ NULL,
                                connectivity_thread,
                                /* arg = */ (void *)0, "connectivity");
  if (status != 0) {
    connectivity_thread_loop = 0;
    ERROR("connectivity plugin: Starting thread failed.");
    pthread_mutex_unlock(&connectivity_lock);
    mnl_socket_close(sock);
    return (-1);
  }

  pthread_mutex_unlock(&connectivity_lock);
  return (0);
} /* }}} int start_thread */

static int stop_thread(int shutdown) /* {{{ */
{
  int status;

  if (sock != NULL)
    mnl_socket_close(sock);

  pthread_mutex_lock(&connectivity_lock);

  if (connectivity_thread_loop == 0) {
    pthread_mutex_unlock(&connectivity_lock);
    return (-1);
  }

  connectivity_thread_loop = 0;
  pthread_cond_broadcast(&connectivity_cond);
  pthread_mutex_unlock(&connectivity_lock);

  if (shutdown == 1) {
    // Since the thread is blocking, calling pthread_join
    // doesn't actually succeed in stopping it.  It will stick around
    // until a NETLINK message is received on the socket (at which
    // it will realize that "connectivity_thread_loop" is 0 and will
    // break out of the read loop and be allowed to die).  This is
    // fine when the process isn't supposed to be exiting, but in
    // the case of a process shutdown, we don't want to have an
    // idle thread hanging around.  Calling pthread_cancel here in
    // the case of a shutdown is just assures that the thread is
    // gone and that the process has been fully terminated.

    DEBUG("connectivity plugin: Canceling thread for process shutdown");

    status = pthread_cancel(connectivity_thread_id);

    if (status != 0) {
      ERROR("connectivity plugin: Unable to cancel thread: %d", status);
      status = -1;
    }
  } else {
    status = pthread_join(connectivity_thread_id, /* return = */ NULL);
    if (status != 0) {
      ERROR("connectivity plugin: Stopping thread failed.");
      status = -1;
    }
  }

  pthread_mutex_lock(&connectivity_lock);
  memset(&connectivity_thread_id, 0, sizeof(connectivity_thread_id));
  connectivity_thread_error = 0;
  pthread_mutex_unlock(&connectivity_lock);

  DEBUG("connectivity plugin: Finished requesting stop of thread");

  return (status);
} /* }}} int stop_thread */

static int connectivity_init(void) /* {{{ */
{
  if (monitor_all_interfaces) {
    NOTICE("connectivity plugin: No interfaces have been selected, so all will "
           "be monitored");
  }

  return (start_thread());
} /* }}} int connectivity_init */

static int connectivity_config(const char *key, const char *value) /* {{{ */
{
  if (ignorelist == NULL) {
    ignorelist = ignorelist_create(/* invert = */ 1);
  }

  if (strcasecmp(key, "Interface") == 0) {
    ignorelist_add(ignorelist, value);
    monitor_all_interfaces = 0;
  } else if (strcasecmp(key, "SendMetrics") == 0) {
    if (IS_TRUE(value)) {
      send_metrics = 1;
    }
  } else {
    return (-1);
  }

  return (0);
} /* }}} int connectivity_config */

static void connectivity_dispatch_notification(
    const char *interface, const char *type, /* {{{ */
    gauge_t value, gauge_t old_value, long long unsigned int timestamp) {

  notification_t n = {
      NOTIF_FAILURE, cdtime(), "", "", "connectivity", "", "", "", NULL};

  if (value == LINK_STATE_UP)
    n.severity = NOTIF_OKAY;

  sstrncpy(n.host, hostname_g, sizeof(n.host));
  sstrncpy(n.plugin_instance, interface, sizeof(n.plugin_instance));
  sstrncpy(n.type, "gauge", sizeof(n.type));
  sstrncpy(n.type_instance, "interface_status", sizeof(n.type_instance));

  gen_metadata_payload(value, old_value, interface, timestamp, &n);

  DEBUG("connectivity plugin: dispatching state %d for interface %s",
        (int)value, interface);

  plugin_dispatch_notification(&n);
  plugin_notification_meta_free(n.meta);
}

static void connectivity_submit(const char *dev, const char *type, /* {{{ */
                   gauge_t value) {
  value_list_t vl = VALUE_LIST_INIT;

  vl.values = &(value_t){.gauge = value};
  vl.values_len = 1;
  sstrncpy(vl.plugin, "connectivity", sizeof(vl.plugin));
  sstrncpy(vl.plugin_instance, dev, sizeof(vl.plugin_instance));
  sstrncpy(vl.type, type, sizeof(vl.type));

  DEBUG("connectivity plugin: dispatching state %d for interface %s", (int)value,
        dev);

  // Create metadata to store JSON key-values
  meta_data_t *meta = meta_data_create();

  vl.meta = meta;

  meta_data_add_string(meta, "entity", dev);

  plugin_dispatch_values(&vl);

  meta_data_destroy(meta);
} /* }}} void interface_submit */

static int connectivity_read(void) /* {{{ */
{
  if (connectivity_thread_error != 0) {
    ERROR("connectivity plugin: The interface thread had a problem. Restarting "
          "it.");

    stop_thread(0);

    for (interface_list_t *il = interface_list_head; il != NULL;
         il = il->next) {
      il->status = LINK_STATE_UNKNOWN;
      il->prev_status = LINK_STATE_UNKNOWN;
      il->sent = 0;
    }

    start_thread();

    return (-1);
  } /* if (connectivity_thread_error != 0) */

  for (interface_list_t *il = interface_list_head; il != NULL;
       il = il->next) /* {{{ */
  {
    uint32_t status;
    uint32_t prev_status;
    uint32_t sent;

    pthread_mutex_lock(&connectivity_lock);

    status = il->status;
    prev_status = il->prev_status;
    sent = il->sent;

    if (status != prev_status && sent == 0) {
      connectivity_dispatch_notification(il->interface, "gauge", status,
                                         prev_status, il->timestamp);

      if (send_metrics == 1)
      {
        connectivity_submit(il->interface, "gauge", status);
      }

      il->sent = 1;
    }

    pthread_mutex_unlock(&connectivity_lock);
  } /* }}} for (il = interface_list_head; il != NULL; il = il->next) */

  return (0);
} /* }}} int connectivity_read */

static int connectivity_shutdown(void) /* {{{ */
{
  interface_list_t *il;

  DEBUG("connectivity plugin: Shutting down thread.");
  if (stop_thread(1) < 0)
    return (-1);

  il = interface_list_head;
  while (il != NULL) {
    interface_list_t *il_next;

    il_next = il->next;

    sfree(il->interface);
    sfree(il);

    il = il_next;
  }

  ignorelist_free(ignorelist);

  return (0);
} /* }}} int connectivity_shutdown */

void module_register(void) {
  plugin_register_config("connectivity", connectivity_config, config_keys,
                         config_keys_num);
  plugin_register_init("connectivity", connectivity_init);
  plugin_register_read("connectivity", connectivity_read);
  plugin_register_shutdown("connectivity", connectivity_shutdown);
} /* void module_register */
