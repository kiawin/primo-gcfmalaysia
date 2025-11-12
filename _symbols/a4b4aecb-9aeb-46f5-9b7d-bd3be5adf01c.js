// Hero with form - Updated November 12, 2025
function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

const exports$1 = {}; const module = { exports: exports$1 };

/*! Axios v1.13.2 Copyright (c) 2025 Matt Zabriskie and contributors */
!function(e,t){"object"==typeof exports$1&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):(e="undefined"!=typeof globalThis?globalThis:e||self).axios=t();}(undefined,(function(){function e(e){var r,n;function o(r,n){try{var a=e[r](n),u=a.value,s=u instanceof t;Promise.resolve(s?u.v:u).then((function(t){if(s){var n="return"===r?"return":"next";if(!u.k||t.done)return o(n,t);t=e[n](t).value;}i(a.done?"return":"normal",t);}),(function(e){o("throw",e);}));}catch(e){i("throw",e);}}function i(e,t){switch(e){case"return":r.resolve({value:t,done:!0});break;case"throw":r.reject(t);break;default:r.resolve({value:t,done:!1});}(r=r.next)?o(r.key,r.arg):n=null;}this._invoke=function(e,t){return new Promise((function(i,a){var u={key:e,arg:t,resolve:i,reject:a,next:null};n?n=n.next=u:(r=n=u,o(e,t));}))},"function"!=typeof e.return&&(this.return=void 0);}function t(e,t){this.v=e,this.k=t;}function r(e){var r={},n=!1;function o(r,o){return n=!0,o=new Promise((function(t){t(e[r](o));})),{done:!1,value:new t(o,1)}}return r["undefined"!=typeof Symbol&&Symbol.iterator||"@@iterator"]=function(){return this},r.next=function(e){return n?(n=!1,e):o("next",e)},"function"==typeof e.throw&&(r.throw=function(e){if(n)throw n=!1,e;return o("throw",e)}),"function"==typeof e.return&&(r.return=function(e){return n?(n=!1,e):o("return",e)}),r}function n(e){var t,r,n,i=2;for("undefined"!=typeof Symbol&&(r=Symbol.asyncIterator,n=Symbol.iterator);i--;){if(r&&null!=(t=e[r]))return t.call(e);if(n&&null!=(t=e[n]))return new o(t.call(e));r="@@asyncIterator",n="@@iterator";}throw new TypeError("Object is not async iterable")}function o(e){function t(e){if(Object(e)!==e)return Promise.reject(new TypeError(e+" is not an object."));var t=e.done;return Promise.resolve(e.value).then((function(e){return {value:e,done:t}}))}return o=function(e){this.s=e,this.n=e.next;},o.prototype={s:null,n:null,next:function(){return t(this.n.apply(this.s,arguments))},return:function(e){var r=this.s.return;return void 0===r?Promise.resolve({value:e,done:!0}):t(r.apply(this.s,arguments))},throw:function(e){var r=this.s.return;return void 0===r?Promise.reject(e):t(r.apply(this.s,arguments))}},new o(e)}function i(e){return new t(e,0)}function a(e,t){var r=Object.keys(e);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(e);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),r.push.apply(r,n);}return r}function u(e){for(var t=1;t<arguments.length;t++){var r=null!=arguments[t]?arguments[t]:{};t%2?a(Object(r),!0).forEach((function(t){m(e,t,r[t]);})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(r)):a(Object(r)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(r,t));}));}return e}function s(){s=function(){return t};var e,t={},r=Object.prototype,n=r.hasOwnProperty,o=Object.defineProperty||function(e,t,r){e[t]=r.value;},i="function"==typeof Symbol?Symbol:{},a=i.iterator||"@@iterator",u=i.asyncIterator||"@@asyncIterator",c=i.toStringTag||"@@toStringTag";function f(e,t,r){return Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}),e[t]}try{f({},"");}catch(e){f=function(e,t,r){return e[t]=r};}function l(e,t,r,n){var i=t&&t.prototype instanceof m?t:m,a=Object.create(i.prototype),u=new P(n||[]);return o(a,"_invoke",{value:k(e,r,u)}),a}function p(e,t,r){try{return {type:"normal",arg:e.call(t,r)}}catch(e){return {type:"throw",arg:e}}}t.wrap=l;var d="suspendedStart",h="executing",v="completed",y={};function m(){}function b(){}function g(){}var w={};f(w,a,(function(){return this}));var E=Object.getPrototypeOf,O=E&&E(E(L([])));O&&O!==r&&n.call(O,a)&&(w=O);var S=g.prototype=m.prototype=Object.create(w);function x(e){["next","throw","return"].forEach((function(t){f(e,t,(function(e){return this._invoke(t,e)}));}));}function R(e,t){function r(o,i,a,u){var s=p(e[o],e,i);if("throw"!==s.type){var c=s.arg,f=c.value;return f&&"object"==typeof f&&n.call(f,"__await")?t.resolve(f.__await).then((function(e){r("next",e,a,u);}),(function(e){r("throw",e,a,u);})):t.resolve(f).then((function(e){c.value=e,a(c);}),(function(e){return r("throw",e,a,u)}))}u(s.arg);}var i;o(this,"_invoke",{value:function(e,n){function o(){return new t((function(t,o){r(e,n,t,o);}))}return i=i?i.then(o,o):o()}});}function k(t,r,n){var o=d;return function(i,a){if(o===h)throw new Error("Generator is already running");if(o===v){if("throw"===i)throw a;return {value:e,done:!0}}for(n.method=i,n.arg=a;;){var u=n.delegate;if(u){var s=T(u,n);if(s){if(s===y)continue;return s}}if("next"===n.method)n.sent=n._sent=n.arg;else if("throw"===n.method){if(o===d)throw o=v,n.arg;n.dispatchException(n.arg);}else "return"===n.method&&n.abrupt("return",n.arg);o=h;var c=p(t,r,n);if("normal"===c.type){if(o=n.done?v:"suspendedYield",c.arg===y)continue;return {value:c.arg,done:n.done}}"throw"===c.type&&(o=v,n.method="throw",n.arg=c.arg);}}}function T(t,r){var n=r.method,o=t.iterator[n];if(o===e)return r.delegate=null,"throw"===n&&t.iterator.return&&(r.method="return",r.arg=e,T(t,r),"throw"===r.method)||"return"!==n&&(r.method="throw",r.arg=new TypeError("The iterator does not provide a '"+n+"' method")),y;var i=p(o,t.iterator,r.arg);if("throw"===i.type)return r.method="throw",r.arg=i.arg,r.delegate=null,y;var a=i.arg;return a?a.done?(r[t.resultName]=a.value,r.next=t.nextLoc,"return"!==r.method&&(r.method="next",r.arg=e),r.delegate=null,y):a:(r.method="throw",r.arg=new TypeError("iterator result is not an object"),r.delegate=null,y)}function j(e){var t={tryLoc:e[0]};1 in e&&(t.catchLoc=e[1]),2 in e&&(t.finallyLoc=e[2],t.afterLoc=e[3]),this.tryEntries.push(t);}function A(e){var t=e.completion||{};t.type="normal",delete t.arg,e.completion=t;}function P(e){this.tryEntries=[{tryLoc:"root"}],e.forEach(j,this),this.reset(!0);}function L(t){if(t||""===t){var r=t[a];if(r)return r.call(t);if("function"==typeof t.next)return t;if(!isNaN(t.length)){var o=-1,i=function r(){for(;++o<t.length;)if(n.call(t,o))return r.value=t[o],r.done=!1,r;return r.value=e,r.done=!0,r};return i.next=i}}throw new TypeError(typeof t+" is not iterable")}return b.prototype=g,o(S,"constructor",{value:g,configurable:!0}),o(g,"constructor",{value:b,configurable:!0}),b.displayName=f(g,c,"GeneratorFunction"),t.isGeneratorFunction=function(e){var t="function"==typeof e&&e.constructor;return !!t&&(t===b||"GeneratorFunction"===(t.displayName||t.name))},t.mark=function(e){return Object.setPrototypeOf?Object.setPrototypeOf(e,g):(e.__proto__=g,f(e,c,"GeneratorFunction")),e.prototype=Object.create(S),e},t.awrap=function(e){return {__await:e}},x(R.prototype),f(R.prototype,u,(function(){return this})),t.AsyncIterator=R,t.async=function(e,r,n,o,i){void 0===i&&(i=Promise);var a=new R(l(e,r,n,o),i);return t.isGeneratorFunction(r)?a:a.next().then((function(e){return e.done?e.value:a.next()}))},x(S),f(S,c,"Generator"),f(S,a,(function(){return this})),f(S,"toString",(function(){return "[object Generator]"})),t.keys=function(e){var t=Object(e),r=[];for(var n in t)r.push(n);return r.reverse(),function e(){for(;r.length;){var n=r.pop();if(n in t)return e.value=n,e.done=!1,e}return e.done=!0,e}},t.values=L,P.prototype={constructor:P,reset:function(t){if(this.prev=0,this.next=0,this.sent=this._sent=e,this.done=!1,this.delegate=null,this.method="next",this.arg=e,this.tryEntries.forEach(A),!t)for(var r in this)"t"===r.charAt(0)&&n.call(this,r)&&!isNaN(+r.slice(1))&&(this[r]=e);},stop:function(){this.done=!0;var e=this.tryEntries[0].completion;if("throw"===e.type)throw e.arg;return this.rval},dispatchException:function(t){if(this.done)throw t;var r=this;function o(n,o){return u.type="throw",u.arg=t,r.next=n,o&&(r.method="next",r.arg=e),!!o}for(var i=this.tryEntries.length-1;i>=0;--i){var a=this.tryEntries[i],u=a.completion;if("root"===a.tryLoc)return o("end");if(a.tryLoc<=this.prev){var s=n.call(a,"catchLoc"),c=n.call(a,"finallyLoc");if(s&&c){if(this.prev<a.catchLoc)return o(a.catchLoc,!0);if(this.prev<a.finallyLoc)return o(a.finallyLoc)}else if(s){if(this.prev<a.catchLoc)return o(a.catchLoc,!0)}else {if(!c)throw new Error("try statement without catch or finally");if(this.prev<a.finallyLoc)return o(a.finallyLoc)}}}},abrupt:function(e,t){for(var r=this.tryEntries.length-1;r>=0;--r){var o=this.tryEntries[r];if(o.tryLoc<=this.prev&&n.call(o,"finallyLoc")&&this.prev<o.finallyLoc){var i=o;break}}i&&("break"===e||"continue"===e)&&i.tryLoc<=t&&t<=i.finallyLoc&&(i=null);var a=i?i.completion:{};return a.type=e,a.arg=t,i?(this.method="next",this.next=i.finallyLoc,y):this.complete(a)},complete:function(e,t){if("throw"===e.type)throw e.arg;return "break"===e.type||"continue"===e.type?this.next=e.arg:"return"===e.type?(this.rval=this.arg=e.arg,this.method="return",this.next="end"):"normal"===e.type&&t&&(this.next=t),y},finish:function(e){for(var t=this.tryEntries.length-1;t>=0;--t){var r=this.tryEntries[t];if(r.finallyLoc===e)return this.complete(r.completion,r.afterLoc),A(r),y}},catch:function(e){for(var t=this.tryEntries.length-1;t>=0;--t){var r=this.tryEntries[t];if(r.tryLoc===e){var n=r.completion;if("throw"===n.type){var o=n.arg;A(r);}return o}}throw new Error("illegal catch attempt")},delegateYield:function(t,r,n){return this.delegate={iterator:L(t),resultName:r,nextLoc:n},"next"===this.method&&(this.arg=e),y}},t}function c(e){var t=function(e,t){if("object"!=typeof e||!e)return e;var r=e[Symbol.toPrimitive];if(void 0!==r){var n=r.call(e,t||"default");if("object"!=typeof n)return n;throw new TypeError("@@toPrimitive must return a primitive value.")}return ("string"===t?String:Number)(e)}(e,"string");return "symbol"==typeof t?t:String(t)}function f(e){return f="function"==typeof Symbol&&"symbol"==typeof Symbol.iterator?function(e){return typeof e}:function(e){return e&&"function"==typeof Symbol&&e.constructor===Symbol&&e!==Symbol.prototype?"symbol":typeof e},f(e)}function l(t){return function(){return new e(t.apply(this,arguments))}}function p(e,t,r,n,o,i,a){try{var u=e[i](a),s=u.value;}catch(e){return void r(e)}u.done?t(s):Promise.resolve(s).then(n,o);}function d(e){return function(){var t=this,r=arguments;return new Promise((function(n,o){var i=e.apply(t,r);function a(e){p(i,n,o,a,u,"next",e);}function u(e){p(i,n,o,a,u,"throw",e);}a(void 0);}))}}function h(e,t){if(!(e instanceof t))throw new TypeError("Cannot call a class as a function")}function v(e,t){for(var r=0;r<t.length;r++){var n=t[r];n.enumerable=n.enumerable||!1,n.configurable=!0,"value"in n&&(n.writable=!0),Object.defineProperty(e,c(n.key),n);}}function y(e,t,r){return t&&v(e.prototype,t),r&&v(e,r),Object.defineProperty(e,"prototype",{writable:!1}),e}function m(e,t,r){return (t=c(t))in e?Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}):e[t]=r,e}function b(e,t){return function(e){if(Array.isArray(e))return e}(e)||function(e,t){var r=null==e?null:"undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(null!=r){var n,o,i,a,u=[],s=!0,c=!1;try{if(i=(r=r.call(e)).next,0===t){if(Object(r)!==r)return;s=!1;}else for(;!(s=(n=i.call(r)).done)&&(u.push(n.value),u.length!==t);s=!0);}catch(e){c=!0,o=e;}finally{try{if(!s&&null!=r.return&&(a=r.return(),Object(a)!==a))return}finally{if(c)throw o}}return u}}(e,t)||w(e,t)||function(){throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function g(e){return function(e){if(Array.isArray(e))return E(e)}(e)||function(e){if("undefined"!=typeof Symbol&&null!=e[Symbol.iterator]||null!=e["@@iterator"])return Array.from(e)}(e)||w(e)||function(){throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function w(e,t){if(e){if("string"==typeof e)return E(e,t);var r=Object.prototype.toString.call(e).slice(8,-1);return "Object"===r&&e.constructor&&(r=e.constructor.name),"Map"===r||"Set"===r?Array.from(e):"Arguments"===r||/^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(r)?E(e,t):void 0}}function E(e,t){(null==t||t>e.length)&&(t=e.length);for(var r=0,n=new Array(t);r<t;r++)n[r]=e[r];return n}function O(e,t){return function(){return e.apply(t,arguments)}}e.prototype["function"==typeof Symbol&&Symbol.asyncIterator||"@@asyncIterator"]=function(){return this},e.prototype.next=function(e){return this._invoke("next",e)},e.prototype.throw=function(e){return this._invoke("throw",e)},e.prototype.return=function(e){return this._invoke("return",e)};var S,x=Object.prototype.toString,R=Object.getPrototypeOf,k=Symbol.iterator,T=Symbol.toStringTag,j=(S=Object.create(null),function(e){var t=x.call(e);return S[t]||(S[t]=t.slice(8,-1).toLowerCase())}),A=function(e){return e=e.toLowerCase(),function(t){return j(t)===e}},P=function(e){return function(t){return f(t)===e}},L=Array.isArray,N=P("undefined");function C(e){return null!==e&&!N(e)&&null!==e.constructor&&!N(e.constructor)&&F(e.constructor.isBuffer)&&e.constructor.isBuffer(e)}var _=A("ArrayBuffer");var U=P("string"),F=P("function"),B=P("number"),D=function(e){return null!==e&&"object"===f(e)},I=function(e){if("object"!==j(e))return !1;var t=R(e);return !(null!==t&&t!==Object.prototype&&null!==Object.getPrototypeOf(t)||T in e||k in e)},q=A("Date"),M=A("File"),z=A("Blob"),H=A("FileList"),J=A("URLSearchParams"),W=b(["ReadableStream","Request","Response","Headers"].map(A),4),K=W[0],V=W[1],G=W[2],X=W[3];function $(e,t){var r,n,o=arguments.length>2&&void 0!==arguments[2]?arguments[2]:{},i=o.allOwnKeys,a=void 0!==i&&i;if(null!=e)if("object"!==f(e)&&(e=[e]),L(e))for(r=0,n=e.length;r<n;r++)t.call(null,e[r],r,e);else {if(C(e))return;var u,s=a?Object.getOwnPropertyNames(e):Object.keys(e),c=s.length;for(r=0;r<c;r++)u=s[r],t.call(null,e[u],u,e);}}function Y(e,t){if(C(e))return null;t=t.toLowerCase();for(var r,n=Object.keys(e),o=n.length;o-- >0;)if(t===(r=n[o]).toLowerCase())return r;return null}var Q="undefined"!=typeof globalThis?globalThis:"undefined"!=typeof self?self:"undefined"!=typeof window?window:global,Z=function(e){return !N(e)&&e!==Q};var ee,te=(ee="undefined"!=typeof Uint8Array&&R(Uint8Array),function(e){return ee&&e instanceof ee}),re=A("HTMLFormElement"),ne=function(e){var t=Object.prototype.hasOwnProperty;return function(e,r){return t.call(e,r)}}(),oe=A("RegExp"),ie=function(e,t){var r=Object.getOwnPropertyDescriptors(e),n={};$(r,(function(r,o){var i;!1!==(i=t(r,o,e))&&(n[o]=i||r);})),Object.defineProperties(e,n);};var ae,ue,se,ce,fe=A("AsyncFunction"),le=(ae="function"==typeof setImmediate,ue=F(Q.postMessage),ae?setImmediate:ue?(se="axios@".concat(Math.random()),ce=[],Q.addEventListener("message",(function(e){var t=e.source,r=e.data;t===Q&&r===se&&ce.length&&ce.shift()();}),!1),function(e){ce.push(e),Q.postMessage(se,"*");}):function(e){return setTimeout(e)}),pe="undefined"!=typeof queueMicrotask?queueMicrotask.bind(Q):"undefined"!=typeof process&&process.nextTick||le,de={isArray:L,isArrayBuffer:_,isBuffer:C,isFormData:function(e){var t;return e&&("function"==typeof FormData&&e instanceof FormData||F(e.append)&&("formdata"===(t=j(e))||"object"===t&&F(e.toString)&&"[object FormData]"===e.toString()))},isArrayBufferView:function(e){return "undefined"!=typeof ArrayBuffer&&ArrayBuffer.isView?ArrayBuffer.isView(e):e&&e.buffer&&_(e.buffer)},isString:U,isNumber:B,isBoolean:function(e){return !0===e||!1===e},isObject:D,isPlainObject:I,isEmptyObject:function(e){if(!D(e)||C(e))return !1;try{return 0===Object.keys(e).length&&Object.getPrototypeOf(e)===Object.prototype}catch(e){return !1}},isReadableStream:K,isRequest:V,isResponse:G,isHeaders:X,isUndefined:N,isDate:q,isFile:M,isBlob:z,isRegExp:oe,isFunction:F,isStream:function(e){return D(e)&&F(e.pipe)},isURLSearchParams:J,isTypedArray:te,isFileList:H,forEach:$,merge:function e(){for(var t=Z(this)&&this||{},r=t.caseless,n=t.skipUndefined,o={},i=function(t,i){var a=r&&Y(o,i)||i;I(o[a])&&I(t)?o[a]=e(o[a],t):I(t)?o[a]=e({},t):L(t)?o[a]=t.slice():n&&N(t)||(o[a]=t);},a=0,u=arguments.length;a<u;a++)arguments[a]&&$(arguments[a],i);return o},extend:function(e,t,r){var n=arguments.length>3&&void 0!==arguments[3]?arguments[3]:{},o=n.allOwnKeys;return $(t,(function(t,n){r&&F(t)?e[n]=O(t,r):e[n]=t;}),{allOwnKeys:o}),e},trim:function(e){return e.trim?e.trim():e.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,"")},stripBOM:function(e){return 65279===e.charCodeAt(0)&&(e=e.slice(1)),e},inherits:function(e,t,r,n){e.prototype=Object.create(t.prototype,n),e.prototype.constructor=e,Object.defineProperty(e,"super",{value:t.prototype}),r&&Object.assign(e.prototype,r);},toFlatObject:function(e,t,r,n){var o,i,a,u={};if(t=t||{},null==e)return t;do{for(i=(o=Object.getOwnPropertyNames(e)).length;i-- >0;)a=o[i],n&&!n(a,e,t)||u[a]||(t[a]=e[a],u[a]=!0);e=!1!==r&&R(e);}while(e&&(!r||r(e,t))&&e!==Object.prototype);return t},kindOf:j,kindOfTest:A,endsWith:function(e,t,r){e=String(e),(void 0===r||r>e.length)&&(r=e.length),r-=t.length;var n=e.indexOf(t,r);return -1!==n&&n===r},toArray:function(e){if(!e)return null;if(L(e))return e;var t=e.length;if(!B(t))return null;for(var r=new Array(t);t-- >0;)r[t]=e[t];return r},forEachEntry:function(e,t){for(var r,n=(e&&e[k]).call(e);(r=n.next())&&!r.done;){var o=r.value;t.call(e,o[0],o[1]);}},matchAll:function(e,t){for(var r,n=[];null!==(r=e.exec(t));)n.push(r);return n},isHTMLForm:re,hasOwnProperty:ne,hasOwnProp:ne,reduceDescriptors:ie,freezeMethods:function(e){ie(e,(function(t,r){if(F(e)&&-1!==["arguments","caller","callee"].indexOf(r))return !1;var n=e[r];F(n)&&(t.enumerable=!1,"writable"in t?t.writable=!1:t.set||(t.set=function(){throw Error("Can not rewrite read-only method '"+r+"'")}));}));},toObjectSet:function(e,t){var r={},n=function(e){e.forEach((function(e){r[e]=!0;}));};return L(e)?n(e):n(String(e).split(t)),r},toCamelCase:function(e){return e.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g,(function(e,t,r){return t.toUpperCase()+r}))},noop:function(){},toFiniteNumber:function(e,t){return null!=e&&Number.isFinite(e=+e)?e:t},findKey:Y,global:Q,isContextDefined:Z,isSpecCompliantForm:function(e){return !!(e&&F(e.append)&&"FormData"===e[T]&&e[k])},toJSONObject:function(e){var t=new Array(10);return function e(r,n){if(D(r)){if(t.indexOf(r)>=0)return;if(C(r))return r;if(!("toJSON"in r)){t[n]=r;var o=L(r)?[]:{};return $(r,(function(t,r){var i=e(t,n+1);!N(i)&&(o[r]=i);})),t[n]=void 0,o}}return r}(e,0)},isAsyncFn:fe,isThenable:function(e){return e&&(D(e)||F(e))&&F(e.then)&&F(e.catch)},setImmediate:le,asap:pe,isIterable:function(e){return null!=e&&F(e[k])}};function he(e,t,r,n,o){Error.call(this),Error.captureStackTrace?Error.captureStackTrace(this,this.constructor):this.stack=(new Error).stack,this.message=e,this.name="AxiosError",t&&(this.code=t),r&&(this.config=r),n&&(this.request=n),o&&(this.response=o,this.status=o.status?o.status:null);}de.inherits(he,Error,{toJSON:function(){return {message:this.message,name:this.name,description:this.description,number:this.number,fileName:this.fileName,lineNumber:this.lineNumber,columnNumber:this.columnNumber,stack:this.stack,config:de.toJSONObject(this.config),code:this.code,status:this.status}}});var ve=he.prototype,ye={};["ERR_BAD_OPTION_VALUE","ERR_BAD_OPTION","ECONNABORTED","ETIMEDOUT","ERR_NETWORK","ERR_FR_TOO_MANY_REDIRECTS","ERR_DEPRECATED","ERR_BAD_RESPONSE","ERR_BAD_REQUEST","ERR_CANCELED","ERR_NOT_SUPPORT","ERR_INVALID_URL"].forEach((function(e){ye[e]={value:e};})),Object.defineProperties(he,ye),Object.defineProperty(ve,"isAxiosError",{value:!0}),he.from=function(e,t,r,n,o,i){var a=Object.create(ve);de.toFlatObject(e,a,(function(e){return e!==Error.prototype}),(function(e){return "isAxiosError"!==e}));var u=e&&e.message?e.message:"Error",s=null==t&&e?e.code:t;return he.call(a,u,s,r,n,o),e&&null==a.cause&&Object.defineProperty(a,"cause",{value:e,configurable:!0}),a.name=e&&e.name||"Error",i&&Object.assign(a,i),a};function me(e){return de.isPlainObject(e)||de.isArray(e)}function be(e){return de.endsWith(e,"[]")?e.slice(0,-2):e}function ge(e,t,r){return e?e.concat(t).map((function(e,t){return e=be(e),!r&&t?"["+e+"]":e})).join(r?".":""):t}var we=de.toFlatObject(de,{},null,(function(e){return /^is[A-Z]/.test(e)}));function Ee(e,t,r){if(!de.isObject(e))throw new TypeError("target must be an object");t=t||new FormData;var n=(r=de.toFlatObject(r,{metaTokens:!0,dots:!1,indexes:!1},!1,(function(e,t){return !de.isUndefined(t[e])}))).metaTokens,o=r.visitor||c,i=r.dots,a=r.indexes,u=(r.Blob||"undefined"!=typeof Blob&&Blob)&&de.isSpecCompliantForm(t);if(!de.isFunction(o))throw new TypeError("visitor must be a function");function s(e){if(null===e)return "";if(de.isDate(e))return e.toISOString();if(de.isBoolean(e))return e.toString();if(!u&&de.isBlob(e))throw new he("Blob is not supported. Use a Buffer instead.");return de.isArrayBuffer(e)||de.isTypedArray(e)?u&&"function"==typeof Blob?new Blob([e]):Buffer.from(e):e}function c(e,r,o){var u=e;if(e&&!o&&"object"===f(e))if(de.endsWith(r,"{}"))r=n?r:r.slice(0,-2),e=JSON.stringify(e);else if(de.isArray(e)&&function(e){return de.isArray(e)&&!e.some(me)}(e)||(de.isFileList(e)||de.endsWith(r,"[]"))&&(u=de.toArray(e)))return r=be(r),u.forEach((function(e,n){!de.isUndefined(e)&&null!==e&&t.append(!0===a?ge([r],n,i):null===a?r:r+"[]",s(e));})),!1;return !!me(e)||(t.append(ge(o,r,i),s(e)),!1)}var l=[],p=Object.assign(we,{defaultVisitor:c,convertValue:s,isVisitable:me});if(!de.isObject(e))throw new TypeError("data must be an object");return function e(r,n){if(!de.isUndefined(r)){if(-1!==l.indexOf(r))throw Error("Circular reference detected in "+n.join("."));l.push(r),de.forEach(r,(function(r,i){!0===(!(de.isUndefined(r)||null===r)&&o.call(t,r,de.isString(i)?i.trim():i,n,p))&&e(r,n?n.concat(i):[i]);})),l.pop();}}(e),t}function Oe(e){var t={"!":"%21","'":"%27","(":"%28",")":"%29","~":"%7E","%20":"+","%00":"\0"};return encodeURIComponent(e).replace(/[!'()~]|%20|%00/g,(function(e){return t[e]}))}function Se(e,t){this._pairs=[],e&&Ee(e,this,t);}var xe=Se.prototype;function Re(e){return encodeURIComponent(e).replace(/%3A/gi,":").replace(/%24/g,"$").replace(/%2C/gi,",").replace(/%20/g,"+")}function ke(e,t,r){if(!t)return e;var n=r&&r.encode||Re;de.isFunction(r)&&(r={serialize:r});var o,i=r&&r.serialize;if(o=i?i(t,r):de.isURLSearchParams(t)?t.toString():new Se(t,r).toString(n)){var a=e.indexOf("#");-1!==a&&(e=e.slice(0,a)),e+=(-1===e.indexOf("?")?"?":"&")+o;}return e}xe.append=function(e,t){this._pairs.push([e,t]);},xe.toString=function(e){var t=e?function(t){return e.call(this,t,Oe)}:Oe;return this._pairs.map((function(e){return t(e[0])+"="+t(e[1])}),"").join("&")};var Te=function(){function e(){h(this,e),this.handlers=[];}return y(e,[{key:"use",value:function(e,t,r){return this.handlers.push({fulfilled:e,rejected:t,synchronous:!!r&&r.synchronous,runWhen:r?r.runWhen:null}),this.handlers.length-1}},{key:"eject",value:function(e){this.handlers[e]&&(this.handlers[e]=null);}},{key:"clear",value:function(){this.handlers&&(this.handlers=[]);}},{key:"forEach",value:function(e){de.forEach(this.handlers,(function(t){null!==t&&e(t);}));}}]),e}(),je={silentJSONParsing:!0,forcedJSONParsing:!0,clarifyTimeoutError:!1},Ae={isBrowser:!0,classes:{URLSearchParams:"undefined"!=typeof URLSearchParams?URLSearchParams:Se,FormData:"undefined"!=typeof FormData?FormData:null,Blob:"undefined"!=typeof Blob?Blob:null},protocols:["http","https","file","blob","url","data"]},Pe="undefined"!=typeof window&&"undefined"!=typeof document,Le="object"===("undefined"==typeof navigator?"undefined":f(navigator))&&navigator||void 0,Ne=Pe&&(!Le||["ReactNative","NativeScript","NS"].indexOf(Le.product)<0),Ce="undefined"!=typeof WorkerGlobalScope&&self instanceof WorkerGlobalScope&&"function"==typeof self.importScripts,_e=Pe&&window.location.href||"http://localhost",Ue=u(u({},Object.freeze({__proto__:null,hasBrowserEnv:Pe,hasStandardBrowserWebWorkerEnv:Ce,hasStandardBrowserEnv:Ne,navigator:Le,origin:_e})),Ae);function Fe(e){function t(e,r,n,o){var i=e[o++];if("__proto__"===i)return !0;var a=Number.isFinite(+i),u=o>=e.length;return i=!i&&de.isArray(n)?n.length:i,u?(de.hasOwnProp(n,i)?n[i]=[n[i],r]:n[i]=r,!a):(n[i]&&de.isObject(n[i])||(n[i]=[]),t(e,r,n[i],o)&&de.isArray(n[i])&&(n[i]=function(e){var t,r,n={},o=Object.keys(e),i=o.length;for(t=0;t<i;t++)n[r=o[t]]=e[r];return n}(n[i])),!a)}if(de.isFormData(e)&&de.isFunction(e.entries)){var r={};return de.forEachEntry(e,(function(e,n){t(function(e){return de.matchAll(/\w+|\[(\w*)]/g,e).map((function(e){return "[]"===e[0]?"":e[1]||e[0]}))}(e),n,r,0);})),r}return null}var Be={transitional:je,adapter:["xhr","http","fetch"],transformRequest:[function(e,t){var r,n=t.getContentType()||"",o=n.indexOf("application/json")>-1,i=de.isObject(e);if(i&&de.isHTMLForm(e)&&(e=new FormData(e)),de.isFormData(e))return o?JSON.stringify(Fe(e)):e;if(de.isArrayBuffer(e)||de.isBuffer(e)||de.isStream(e)||de.isFile(e)||de.isBlob(e)||de.isReadableStream(e))return e;if(de.isArrayBufferView(e))return e.buffer;if(de.isURLSearchParams(e))return t.setContentType("application/x-www-form-urlencoded;charset=utf-8",!1),e.toString();if(i){if(n.indexOf("application/x-www-form-urlencoded")>-1)return function(e,t){return Ee(e,new Ue.classes.URLSearchParams,u({visitor:function(e,t,r,n){return Ue.isNode&&de.isBuffer(e)?(this.append(t,e.toString("base64")),!1):n.defaultVisitor.apply(this,arguments)}},t))}(e,this.formSerializer).toString();if((r=de.isFileList(e))||n.indexOf("multipart/form-data")>-1){var a=this.env&&this.env.FormData;return Ee(r?{"files[]":e}:e,a&&new a,this.formSerializer)}}return i||o?(t.setContentType("application/json",!1),function(e,t,r){if(de.isString(e))try{return (t||JSON.parse)(e),de.trim(e)}catch(e){if("SyntaxError"!==e.name)throw e}return (r||JSON.stringify)(e)}(e)):e}],transformResponse:[function(e){var t=this.transitional||Be.transitional,r=t&&t.forcedJSONParsing,n="json"===this.responseType;if(de.isResponse(e)||de.isReadableStream(e))return e;if(e&&de.isString(e)&&(r&&!this.responseType||n)){var o=!(t&&t.silentJSONParsing)&&n;try{return JSON.parse(e,this.parseReviver)}catch(e){if(o){if("SyntaxError"===e.name)throw he.from(e,he.ERR_BAD_RESPONSE,this,null,this.response);throw e}}}return e}],timeout:0,xsrfCookieName:"XSRF-TOKEN",xsrfHeaderName:"X-XSRF-TOKEN",maxContentLength:-1,maxBodyLength:-1,env:{FormData:Ue.classes.FormData,Blob:Ue.classes.Blob},validateStatus:function(e){return e>=200&&e<300},headers:{common:{Accept:"application/json, text/plain, */*","Content-Type":void 0}}};de.forEach(["delete","get","head","post","put","patch"],(function(e){Be.headers[e]={};}));var De=Be,Ie=de.toObjectSet(["age","authorization","content-length","content-type","etag","expires","from","host","if-modified-since","if-unmodified-since","last-modified","location","max-forwards","proxy-authorization","referer","retry-after","user-agent"]),qe=Symbol("internals");function Me(e){return e&&String(e).trim().toLowerCase()}function ze(e){return !1===e||null==e?e:de.isArray(e)?e.map(ze):String(e)}function He(e,t,r,n,o){return de.isFunction(n)?n.call(this,t,r):(o&&(t=r),de.isString(t)?de.isString(n)?-1!==t.indexOf(n):de.isRegExp(n)?n.test(t):void 0:void 0)}var Je=function(e,t){function r(e){h(this,r),e&&this.set(e);}return y(r,[{key:"set",value:function(e,t,r){var n=this;function o(e,t,r){var o=Me(t);if(!o)throw new Error("header name must be a non-empty string");var i=de.findKey(n,o);(!i||void 0===n[i]||!0===r||void 0===r&&!1!==n[i])&&(n[i||t]=ze(e));}var i=function(e,t){return de.forEach(e,(function(e,r){return o(e,r,t)}))};if(de.isPlainObject(e)||e instanceof this.constructor)i(e,t);else if(de.isString(e)&&(e=e.trim())&&!/^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(e.trim()))i(function(e){var t,r,n,o={};return e&&e.split("\n").forEach((function(e){n=e.indexOf(":"),t=e.substring(0,n).trim().toLowerCase(),r=e.substring(n+1).trim(),!t||o[t]&&Ie[t]||("set-cookie"===t?o[t]?o[t].push(r):o[t]=[r]:o[t]=o[t]?o[t]+", "+r:r);})),o}(e),t);else if(de.isObject(e)&&de.isIterable(e)){var a,u,s,c={},f=function(e,t){var r="undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(!r){if(Array.isArray(e)||(r=w(e))||t&&e&&"number"==typeof e.length){r&&(e=r);var n=0,o=function(){};return {s:o,n:function(){return n>=e.length?{done:!0}:{done:!1,value:e[n++]}},e:function(e){throw e},f:o}}throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}var i,a=!0,u=!1;return {s:function(){r=r.call(e);},n:function(){var e=r.next();return a=e.done,e},e:function(e){u=!0,i=e;},f:function(){try{a||null==r.return||r.return();}finally{if(u)throw i}}}}(e);try{for(f.s();!(s=f.n()).done;){var l=s.value;if(!de.isArray(l))throw TypeError("Object iterator must return a key-value pair");c[u=l[0]]=(a=c[u])?de.isArray(a)?[].concat(g(a),[l[1]]):[a,l[1]]:l[1];}}catch(e){f.e(e);}finally{f.f();}i(c,t);}else null!=e&&o(t,e,r);return this}},{key:"get",value:function(e,t){if(e=Me(e)){var r=de.findKey(this,e);if(r){var n=this[r];if(!t)return n;if(!0===t)return function(e){for(var t,r=Object.create(null),n=/([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;t=n.exec(e);)r[t[1]]=t[2];return r}(n);if(de.isFunction(t))return t.call(this,n,r);if(de.isRegExp(t))return t.exec(n);throw new TypeError("parser must be boolean|regexp|function")}}}},{key:"has",value:function(e,t){if(e=Me(e)){var r=de.findKey(this,e);return !(!r||void 0===this[r]||t&&!He(0,this[r],r,t))}return !1}},{key:"delete",value:function(e,t){var r=this,n=!1;function o(e){if(e=Me(e)){var o=de.findKey(r,e);!o||t&&!He(0,r[o],o,t)||(delete r[o],n=!0);}}return de.isArray(e)?e.forEach(o):o(e),n}},{key:"clear",value:function(e){for(var t=Object.keys(this),r=t.length,n=!1;r--;){var o=t[r];e&&!He(0,this[o],o,e,!0)||(delete this[o],n=!0);}return n}},{key:"normalize",value:function(e){var t=this,r={};return de.forEach(this,(function(n,o){var i=de.findKey(r,o);if(i)return t[i]=ze(n),void delete t[o];var a=e?function(e){return e.trim().toLowerCase().replace(/([a-z\d])(\w*)/g,(function(e,t,r){return t.toUpperCase()+r}))}(o):String(o).trim();a!==o&&delete t[o],t[a]=ze(n),r[a]=!0;})),this}},{key:"concat",value:function(){for(var e,t=arguments.length,r=new Array(t),n=0;n<t;n++)r[n]=arguments[n];return (e=this.constructor).concat.apply(e,[this].concat(r))}},{key:"toJSON",value:function(e){var t=Object.create(null);return de.forEach(this,(function(r,n){null!=r&&!1!==r&&(t[n]=e&&de.isArray(r)?r.join(", "):r);})),t}},{key:Symbol.iterator,value:function(){return Object.entries(this.toJSON())[Symbol.iterator]()}},{key:"toString",value:function(){return Object.entries(this.toJSON()).map((function(e){var t=b(e,2);return t[0]+": "+t[1]})).join("\n")}},{key:"getSetCookie",value:function(){return this.get("set-cookie")||[]}},{key:Symbol.toStringTag,get:function(){return "AxiosHeaders"}}],[{key:"from",value:function(e){return e instanceof this?e:new this(e)}},{key:"concat",value:function(e){for(var t=new this(e),r=arguments.length,n=new Array(r>1?r-1:0),o=1;o<r;o++)n[o-1]=arguments[o];return n.forEach((function(e){return t.set(e)})),t}},{key:"accessor",value:function(e){var t=(this[qe]=this[qe]={accessors:{}}).accessors,r=this.prototype;function n(e){var n=Me(e);t[n]||(!function(e,t){var r=de.toCamelCase(" "+t);["get","set","has"].forEach((function(n){Object.defineProperty(e,n+r,{value:function(e,r,o){return this[n].call(this,t,e,r,o)},configurable:!0});}));}(r,e),t[n]=!0);}return de.isArray(e)?e.forEach(n):n(e),this}}]),r}();Je.accessor(["Content-Type","Content-Length","Accept","Accept-Encoding","User-Agent","Authorization"]),de.reduceDescriptors(Je.prototype,(function(e,t){var r=e.value,n=t[0].toUpperCase()+t.slice(1);return {get:function(){return r},set:function(e){this[n]=e;}}})),de.freezeMethods(Je);var We=Je;function Ke(e,t){var r=this||De,n=t||r,o=We.from(n.headers),i=n.data;return de.forEach(e,(function(e){i=e.call(r,i,o.normalize(),t?t.status:void 0);})),o.normalize(),i}function Ve(e){return !(!e||!e.__CANCEL__)}function Ge(e,t,r){he.call(this,null==e?"canceled":e,he.ERR_CANCELED,t,r),this.name="CanceledError";}function Xe(e,t,r){var n=r.config.validateStatus;r.status&&n&&!n(r.status)?t(new he("Request failed with status code "+r.status,[he.ERR_BAD_REQUEST,he.ERR_BAD_RESPONSE][Math.floor(r.status/100)-4],r.config,r.request,r)):e(r);}function $e(e,t){e=e||10;var r,n=new Array(e),o=new Array(e),i=0,a=0;return t=void 0!==t?t:1e3,function(u){var s=Date.now(),c=o[a];r||(r=s),n[i]=u,o[i]=s;for(var f=a,l=0;f!==i;)l+=n[f++],f%=e;if((i=(i+1)%e)===a&&(a=(a+1)%e),!(s-r<t)){var p=c&&s-c;return p?Math.round(1e3*l/p):void 0}}}function Ye(e,t){var r,n,o=0,i=1e3/t,a=function(t){var i=arguments.length>1&&void 0!==arguments[1]?arguments[1]:Date.now();o=i,r=null,n&&(clearTimeout(n),n=null),e.apply(void 0,g(t));};return [function(){for(var e=Date.now(),t=e-o,u=arguments.length,s=new Array(u),c=0;c<u;c++)s[c]=arguments[c];t>=i?a(s,e):(r=s,n||(n=setTimeout((function(){n=null,a(r);}),i-t)));},function(){return r&&a(r)}]}de.inherits(Ge,he,{__CANCEL__:!0});var Qe=function(e,t){var r=arguments.length>2&&void 0!==arguments[2]?arguments[2]:3,n=0,o=$e(50,250);return Ye((function(r){var i=r.loaded,a=r.lengthComputable?r.total:void 0,u=i-n,s=o(u);n=i;var c=m({loaded:i,total:a,progress:a?i/a:void 0,bytes:u,rate:s||void 0,estimated:s&&a&&i<=a?(a-i)/s:void 0,event:r,lengthComputable:null!=a},t?"download":"upload",!0);e(c);}),r)},Ze=function(e,t){var r=null!=e;return [function(n){return t[0]({lengthComputable:r,total:e,loaded:n})},t[1]]},et=function(e){return function(){for(var t=arguments.length,r=new Array(t),n=0;n<t;n++)r[n]=arguments[n];return de.asap((function(){return e.apply(void 0,r)}))}},tt=Ue.hasStandardBrowserEnv?function(e,t){return function(r){return r=new URL(r,Ue.origin),e.protocol===r.protocol&&e.host===r.host&&(t||e.port===r.port)}}(new URL(Ue.origin),Ue.navigator&&/(msie|trident)/i.test(Ue.navigator.userAgent)):function(){return !0},rt=Ue.hasStandardBrowserEnv?{write:function(e,t,r,n,o,i,a){if("undefined"!=typeof document){var u=["".concat(e,"=").concat(encodeURIComponent(t))];de.isNumber(r)&&u.push("expires=".concat(new Date(r).toUTCString())),de.isString(n)&&u.push("path=".concat(n)),de.isString(o)&&u.push("domain=".concat(o)),!0===i&&u.push("secure"),de.isString(a)&&u.push("SameSite=".concat(a)),document.cookie=u.join("; ");}},read:function(e){if("undefined"==typeof document)return null;var t=document.cookie.match(new RegExp("(?:^|; )"+e+"=([^;]*)"));return t?decodeURIComponent(t[1]):null},remove:function(e){this.write(e,"",Date.now()-864e5,"/");}}:{write:function(){},read:function(){return null},remove:function(){}};function nt(e,t,r){var n=!/^([a-z][a-z\d+\-.]*:)?\/\//i.test(t);return e&&(n||0==r)?function(e,t){return t?e.replace(/\/?\/$/,"")+"/"+t.replace(/^\/+/,""):e}(e,t):t}var ot=function(e){return e instanceof We?u({},e):e};function it(e,t){t=t||{};var r={};function n(e,t,r,n){return de.isPlainObject(e)&&de.isPlainObject(t)?de.merge.call({caseless:n},e,t):de.isPlainObject(t)?de.merge({},t):de.isArray(t)?t.slice():t}function o(e,t,r,o){return de.isUndefined(t)?de.isUndefined(e)?void 0:n(void 0,e,0,o):n(e,t,0,o)}function i(e,t){if(!de.isUndefined(t))return n(void 0,t)}function a(e,t){return de.isUndefined(t)?de.isUndefined(e)?void 0:n(void 0,e):n(void 0,t)}function s(r,o,i){return i in t?n(r,o):i in e?n(void 0,r):void 0}var c={url:i,method:i,data:i,baseURL:a,transformRequest:a,transformResponse:a,paramsSerializer:a,timeout:a,timeoutMessage:a,withCredentials:a,withXSRFToken:a,adapter:a,responseType:a,xsrfCookieName:a,xsrfHeaderName:a,onUploadProgress:a,onDownloadProgress:a,decompress:a,maxContentLength:a,maxBodyLength:a,beforeRedirect:a,transport:a,httpAgent:a,httpsAgent:a,cancelToken:a,socketPath:a,responseEncoding:a,validateStatus:s,headers:function(e,t,r){return o(ot(e),ot(t),0,!0)}};return de.forEach(Object.keys(u(u({},e),t)),(function(n){var i=c[n]||o,a=i(e[n],t[n],n);de.isUndefined(a)&&i!==s||(r[n]=a);})),r}var at,ut=function(e){var t=it({},e),r=t.data,n=t.withXSRFToken,o=t.xsrfHeaderName,i=t.xsrfCookieName,a=t.headers,u=t.auth;if(t.headers=a=We.from(a),t.url=ke(nt(t.baseURL,t.url,t.allowAbsoluteUrls),e.params,e.paramsSerializer),u&&a.set("Authorization","Basic "+btoa((u.username||"")+":"+(u.password?unescape(encodeURIComponent(u.password)):""))),de.isFormData(r))if(Ue.hasStandardBrowserEnv||Ue.hasStandardBrowserWebWorkerEnv)a.setContentType(void 0);else if(de.isFunction(r.getHeaders)){var s=r.getHeaders(),c=["content-type","content-length"];Object.entries(s).forEach((function(e){var t=b(e,2),r=t[0],n=t[1];c.includes(r.toLowerCase())&&a.set(r,n);}));}if(Ue.hasStandardBrowserEnv&&(n&&de.isFunction(n)&&(n=n(t)),n||!1!==n&&tt(t.url))){var f=o&&i&&rt.read(i);f&&a.set(o,f);}return t},st="undefined"!=typeof XMLHttpRequest&&function(e){return new Promise((function(t,r){var n,o,i,a,u,s=ut(e),c=s.data,f=We.from(s.headers).normalize(),l=s.responseType,p=s.onUploadProgress,d=s.onDownloadProgress;function h(){a&&a(),u&&u(),s.cancelToken&&s.cancelToken.unsubscribe(n),s.signal&&s.signal.removeEventListener("abort",n);}var v=new XMLHttpRequest;function y(){if(v){var n=We.from("getAllResponseHeaders"in v&&v.getAllResponseHeaders());Xe((function(e){t(e),h();}),(function(e){r(e),h();}),{data:l&&"text"!==l&&"json"!==l?v.response:v.responseText,status:v.status,statusText:v.statusText,headers:n,config:e,request:v}),v=null;}}if(v.open(s.method.toUpperCase(),s.url,!0),v.timeout=s.timeout,"onloadend"in v?v.onloadend=y:v.onreadystatechange=function(){v&&4===v.readyState&&(0!==v.status||v.responseURL&&0===v.responseURL.indexOf("file:"))&&setTimeout(y);},v.onabort=function(){v&&(r(new he("Request aborted",he.ECONNABORTED,e,v)),v=null);},v.onerror=function(t){var n=new he(t&&t.message?t.message:"Network Error",he.ERR_NETWORK,e,v);n.event=t||null,r(n),v=null;},v.ontimeout=function(){var t=s.timeout?"timeout of "+s.timeout+"ms exceeded":"timeout exceeded",n=s.transitional||je;s.timeoutErrorMessage&&(t=s.timeoutErrorMessage),r(new he(t,n.clarifyTimeoutError?he.ETIMEDOUT:he.ECONNABORTED,e,v)),v=null;},void 0===c&&f.setContentType(null),"setRequestHeader"in v&&de.forEach(f.toJSON(),(function(e,t){v.setRequestHeader(t,e);})),de.isUndefined(s.withCredentials)||(v.withCredentials=!!s.withCredentials),l&&"json"!==l&&(v.responseType=s.responseType),d){var m=b(Qe(d,!0),2);i=m[0],u=m[1],v.addEventListener("progress",i);}if(p&&v.upload){var g=b(Qe(p),2);o=g[0],a=g[1],v.upload.addEventListener("progress",o),v.upload.addEventListener("loadend",a);}(s.cancelToken||s.signal)&&(n=function(t){v&&(r(!t||t.type?new Ge(null,e,v):t),v.abort(),v=null);},s.cancelToken&&s.cancelToken.subscribe(n),s.signal&&(s.signal.aborted?n():s.signal.addEventListener("abort",n)));var w,E,O=(w=s.url,(E=/^([-+\w]{1,25})(:?\/\/|:)/.exec(w))&&E[1]||"");O&&-1===Ue.protocols.indexOf(O)?r(new he("Unsupported protocol "+O+":",he.ERR_BAD_REQUEST,e)):v.send(c||null);}))},ct=function(e,t){var r=(e=e?e.filter(Boolean):[]).length;if(t||r){var n,o=new AbortController,i=function(e){if(!n){n=!0,u();var t=e instanceof Error?e:this.reason;o.abort(t instanceof he?t:new Ge(t instanceof Error?t.message:t));}},a=t&&setTimeout((function(){a=null,i(new he("timeout ".concat(t," of ms exceeded"),he.ETIMEDOUT));}),t),u=function(){e&&(a&&clearTimeout(a),a=null,e.forEach((function(e){e.unsubscribe?e.unsubscribe(i):e.removeEventListener("abort",i);})),e=null);};e.forEach((function(e){return e.addEventListener("abort",i)}));var s=o.signal;return s.unsubscribe=function(){return de.asap(u)},s}},ft=s().mark((function e(t,r){var n,o,i;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(n=t.byteLength,r&&!(n<r)){e.next=5;break}return e.next=4,t;case 4:return e.abrupt("return");case 5:o=0;case 6:if(!(o<n)){e.next=13;break}return i=o+r,e.next=10,t.slice(o,i);case 10:o=i,e.next=6;break;case 13:case"end":return e.stop()}}),e)})),lt=function(){var e=l(s().mark((function e(t,o){var a,u,c,f,l,p;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:a=!1,u=!1,e.prev=2,f=n(pt(t));case 4:return e.next=6,i(f.next());case 6:if(!(a=!(l=e.sent).done)){e.next=12;break}return p=l.value,e.delegateYield(r(n(ft(p,o))),"t0",9);case 9:a=!1,e.next=4;break;case 12:e.next=18;break;case 14:e.prev=14,e.t1=e.catch(2),u=!0,c=e.t1;case 18:if(e.prev=18,e.prev=19,!a||null==f.return){e.next=23;break}return e.next=23,i(f.return());case 23:if(e.prev=23,!u){e.next=26;break}throw c;case 26:return e.finish(23);case 27:return e.finish(18);case 28:case"end":return e.stop()}}),e,null,[[2,14,18,28],[19,,23,27]])})));return function(t,r){return e.apply(this,arguments)}}(),pt=function(){var e=l(s().mark((function e(t){var o,a,u,c;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(!t[Symbol.asyncIterator]){e.next=3;break}return e.delegateYield(r(n(t)),"t0",2);case 2:return e.abrupt("return");case 3:o=t.getReader(),e.prev=4;case 5:return e.next=7,i(o.read());case 7:if(a=e.sent,u=a.done,c=a.value,!u){e.next=12;break}return e.abrupt("break",16);case 12:return e.next=14,c;case 14:e.next=5;break;case 16:return e.prev=16,e.next=19,i(o.cancel());case 19:return e.finish(16);case 20:case"end":return e.stop()}}),e,null,[[4,,16,20]])})));return function(t){return e.apply(this,arguments)}}(),dt=function(e,t,r,n){var o,i=lt(e,t),a=0,u=function(e){o||(o=!0,n&&n(e));};return new ReadableStream({pull:function(e){return d(s().mark((function t(){var n,o,c,f,l;return s().wrap((function(t){for(;;)switch(t.prev=t.next){case 0:return t.prev=0,t.next=3,i.next();case 3:if(n=t.sent,o=n.done,c=n.value,!o){t.next=10;break}return u(),e.close(),t.abrupt("return");case 10:f=c.byteLength,r&&(l=a+=f,r(l)),e.enqueue(new Uint8Array(c)),t.next=19;break;case 15:throw t.prev=15,t.t0=t.catch(0),u(t.t0),t.t0;case 19:case"end":return t.stop()}}),t,null,[[0,15]])})))()},cancel:function(e){return u(e),i.return()}},{highWaterMark:2})},ht=de.isFunction,vt={Request:(at=de.global).Request,Response:at.Response},yt=de.global,mt=yt.ReadableStream,bt=yt.TextEncoder,gt=function(e){try{for(var t=arguments.length,r=new Array(t>1?t-1:0),n=1;n<t;n++)r[n-1]=arguments[n];return !!e.apply(void 0,r)}catch(e){return !1}},wt=function(e){var t=e=de.merge.call({skipUndefined:!0},vt,e),r=t.fetch,n=t.Request,o=t.Response,i=r?ht(r):"function"==typeof fetch,a=ht(n),c=ht(o);if(!i)return !1;var f,l=i&&ht(mt),p=i&&("function"==typeof bt?(f=new bt,function(e){return f.encode(e)}):function(){var e=d(s().mark((function e(t){return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return e.t0=Uint8Array,e.next=3,new n(t).arrayBuffer();case 3:return e.t1=e.sent,e.abrupt("return",new e.t0(e.t1));case 5:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}()),h=a&&l&&gt((function(){var e=!1,t=new n(Ue.origin,{body:new mt,method:"POST",get duplex(){return e=!0,"half"}}).headers.has("Content-Type");return e&&!t})),v=c&&l&&gt((function(){return de.isReadableStream(new o("").body)})),y={stream:v&&function(e){return e.body}};i&&["text","arrayBuffer","blob","formData","stream"].forEach((function(e){!y[e]&&(y[e]=function(t,r){var n=t&&t[e];if(n)return n.call(t);throw new he("Response type '".concat(e,"' is not supported"),he.ERR_NOT_SUPPORT,r)});}));var m=function(){var e=d(s().mark((function e(t){var r;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(null!=t){e.next=2;break}return e.abrupt("return",0);case 2:if(!de.isBlob(t)){e.next=4;break}return e.abrupt("return",t.size);case 4:if(!de.isSpecCompliantForm(t)){e.next=9;break}return r=new n(Ue.origin,{method:"POST",body:t}),e.next=8,r.arrayBuffer();case 8:case 15:return e.abrupt("return",e.sent.byteLength);case 9:if(!de.isArrayBufferView(t)&&!de.isArrayBuffer(t)){e.next=11;break}return e.abrupt("return",t.byteLength);case 11:if(de.isURLSearchParams(t)&&(t+=""),!de.isString(t)){e.next=16;break}return e.next=15,p(t);case 16:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}(),g=function(){var e=d(s().mark((function e(t,r){var n;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return n=de.toFiniteNumber(t.getContentLength()),e.abrupt("return",null==n?m(r):n);case 2:case"end":return e.stop()}}),e)})));return function(t,r){return e.apply(this,arguments)}}();return function(){var e=d(s().mark((function e(t){var i,c,f,l,p,d,m,w,E,O,S,x,R,k,T,j,A,P,L,N,C,_,U,F,B,D,I,q,M,z,H,J,W,K,V,G;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(i=ut(t),c=i.url,f=i.method,l=i.data,p=i.signal,d=i.cancelToken,m=i.timeout,w=i.onDownloadProgress,E=i.onUploadProgress,O=i.responseType,S=i.headers,x=i.withCredentials,R=void 0===x?"same-origin":x,k=i.fetchOptions,T=r||fetch,O=O?(O+"").toLowerCase():"text",j=ct([p,d&&d.toAbortSignal()],m),A=null,P=j&&j.unsubscribe&&function(){j.unsubscribe();},e.prev=6,e.t0=E&&h&&"get"!==f&&"head"!==f,!e.t0){e.next=13;break}return e.next=11,g(S,l);case 11:e.t1=L=e.sent,e.t0=0!==e.t1;case 13:if(!e.t0){e.next=17;break}N=new n(c,{method:"POST",body:l,duplex:"half"}),de.isFormData(l)&&(C=N.headers.get("content-type"))&&S.setContentType(C),N.body&&(_=Ze(L,Qe(et(E))),U=b(_,2),F=U[0],B=U[1],l=dt(N.body,65536,F,B));case 17:return de.isString(R)||(R=R?"include":"omit"),D=a&&"credentials"in n.prototype,I=u(u({},k),{},{signal:j,method:f.toUpperCase(),headers:S.normalize().toJSON(),body:l,duplex:"half",credentials:D?R:void 0}),A=a&&new n(c,I),e.next=23,a?T(A,k):T(c,I);case 23:return q=e.sent,M=v&&("stream"===O||"response"===O),v&&(w||M&&P)&&(z={},["status","statusText","headers"].forEach((function(e){z[e]=q[e];})),H=de.toFiniteNumber(q.headers.get("content-length")),J=w&&Ze(H,Qe(et(w),!0))||[],W=b(J,2),K=W[0],V=W[1],q=new o(dt(q.body,65536,K,(function(){V&&V(),P&&P();})),z)),O=O||"text",e.next=29,y[de.findKey(y,O)||"text"](q,t);case 29:return G=e.sent,!M&&P&&P(),e.next=33,new Promise((function(e,r){Xe(e,r,{data:G,headers:We.from(q.headers),status:q.status,statusText:q.statusText,config:t,request:A});}));case 33:return e.abrupt("return",e.sent);case 36:if(e.prev=36,e.t2=e.catch(6),P&&P(),!e.t2||"TypeError"!==e.t2.name||!/Load failed|fetch/i.test(e.t2.message)){e.next=41;break}throw Object.assign(new he("Network Error",he.ERR_NETWORK,t,A),{cause:e.t2.cause||e.t2});case 41:throw he.from(e.t2,e.t2&&e.t2.code,t,A);case 42:case"end":return e.stop()}}),e,null,[[6,36]])})));return function(t){return e.apply(this,arguments)}}()},Et=new Map,Ot=function(e){for(var t,r,n=e&&e.env||{},o=n.fetch,i=[n.Request,n.Response,o],a=i.length,u=Et;a--;)t=i[a],void 0===(r=u.get(t))&&u.set(t,r=a?new Map:wt(n)),u=r;return r};Ot();var St={http:null,xhr:st,fetch:{get:Ot}};de.forEach(St,(function(e,t){if(e){try{Object.defineProperty(e,"name",{value:t});}catch(e){}Object.defineProperty(e,"adapterName",{value:t});}}));var xt=function(e){return "- ".concat(e)},Rt=function(e){return de.isFunction(e)||null===e||!1===e};var kt={getAdapter:function(e,t){for(var r,n,o=(e=de.isArray(e)?e:[e]).length,i={},a=0;a<o;a++){var u=void 0;if(n=r=e[a],!Rt(r)&&void 0===(n=St[(u=String(r)).toLowerCase()]))throw new he("Unknown adapter '".concat(u,"'"));if(n&&(de.isFunction(n)||(n=n.get(t))))break;i[u||"#"+a]=n;}if(!n){var s=Object.entries(i).map((function(e){var t=b(e,2),r=t[0],n=t[1];return "adapter ".concat(r," ")+(!1===n?"is not supported by the environment":"is not available in the build")}));throw new he("There is no suitable adapter to dispatch the request "+(o?s.length>1?"since :\n"+s.map(xt).join("\n"):" "+xt(s[0]):"as no adapter specified"),"ERR_NOT_SUPPORT")}return n},adapters:St};function Tt(e){if(e.cancelToken&&e.cancelToken.throwIfRequested(),e.signal&&e.signal.aborted)throw new Ge(null,e)}function jt(e){return Tt(e),e.headers=We.from(e.headers),e.data=Ke.call(e,e.transformRequest),-1!==["post","put","patch"].indexOf(e.method)&&e.headers.setContentType("application/x-www-form-urlencoded",!1),kt.getAdapter(e.adapter||De.adapter,e)(e).then((function(t){return Tt(e),t.data=Ke.call(e,e.transformResponse,t),t.headers=We.from(t.headers),t}),(function(t){return Ve(t)||(Tt(e),t&&t.response&&(t.response.data=Ke.call(e,e.transformResponse,t.response),t.response.headers=We.from(t.response.headers))),Promise.reject(t)}))}var At="1.13.2",Pt={};["object","boolean","number","function","string","symbol"].forEach((function(e,t){Pt[e]=function(r){return f(r)===e||"a"+(t<1?"n ":" ")+e};}));var Lt={};Pt.transitional=function(e,t,r){function n(e,t){return "[Axios v1.13.2] Transitional option '"+e+"'"+t+(r?". "+r:"")}return function(r,o,i){if(!1===e)throw new he(n(o," has been removed"+(t?" in "+t:"")),he.ERR_DEPRECATED);return t&&!Lt[o]&&(Lt[o]=!0,console.warn(n(o," has been deprecated since v"+t+" and will be removed in the near future"))),!e||e(r,o,i)}},Pt.spelling=function(e){return function(t,r){return console.warn("".concat(r," is likely a misspelling of ").concat(e)),!0}};var Nt={assertOptions:function(e,t,r){if("object"!==f(e))throw new he("options must be an object",he.ERR_BAD_OPTION_VALUE);for(var n=Object.keys(e),o=n.length;o-- >0;){var i=n[o],a=t[i];if(a){var u=e[i],s=void 0===u||a(u,i,e);if(!0!==s)throw new he("option "+i+" must be "+s,he.ERR_BAD_OPTION_VALUE)}else if(!0!==r)throw new he("Unknown option "+i,he.ERR_BAD_OPTION)}},validators:Pt},Ct=Nt.validators,_t=function(){function e(t){h(this,e),this.defaults=t||{},this.interceptors={request:new Te,response:new Te};}var t;return y(e,[{key:"request",value:(t=d(s().mark((function e(t,r){var n,o;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return e.prev=0,e.next=3,this._request(t,r);case 3:return e.abrupt("return",e.sent);case 6:if(e.prev=6,e.t0=e.catch(0),e.t0 instanceof Error){n={},Error.captureStackTrace?Error.captureStackTrace(n):n=new Error,o=n.stack?n.stack.replace(/^.+\n/,""):"";try{e.t0.stack?o&&!String(e.t0.stack).endsWith(o.replace(/^.+\n.+\n/,""))&&(e.t0.stack+="\n"+o):e.t0.stack=o;}catch(e){}}throw e.t0;case 10:case"end":return e.stop()}}),e,this,[[0,6]])}))),function(e,r){return t.apply(this,arguments)})},{key:"_request",value:function(e,t){"string"==typeof e?(t=t||{}).url=e:t=e||{};var r=t=it(this.defaults,t),n=r.transitional,o=r.paramsSerializer,i=r.headers;void 0!==n&&Nt.assertOptions(n,{silentJSONParsing:Ct.transitional(Ct.boolean),forcedJSONParsing:Ct.transitional(Ct.boolean),clarifyTimeoutError:Ct.transitional(Ct.boolean)},!1),null!=o&&(de.isFunction(o)?t.paramsSerializer={serialize:o}:Nt.assertOptions(o,{encode:Ct.function,serialize:Ct.function},!0)),void 0!==t.allowAbsoluteUrls||(void 0!==this.defaults.allowAbsoluteUrls?t.allowAbsoluteUrls=this.defaults.allowAbsoluteUrls:t.allowAbsoluteUrls=!0),Nt.assertOptions(t,{baseUrl:Ct.spelling("baseURL"),withXsrfToken:Ct.spelling("withXSRFToken")},!0),t.method=(t.method||this.defaults.method||"get").toLowerCase();var a=i&&de.merge(i.common,i[t.method]);i&&de.forEach(["delete","get","head","post","put","patch","common"],(function(e){delete i[e];})),t.headers=We.concat(a,i);var u=[],s=!0;this.interceptors.request.forEach((function(e){"function"==typeof e.runWhen&&!1===e.runWhen(t)||(s=s&&e.synchronous,u.unshift(e.fulfilled,e.rejected));}));var c,f=[];this.interceptors.response.forEach((function(e){f.push(e.fulfilled,e.rejected);}));var l,p=0;if(!s){var d=[jt.bind(this),void 0];for(d.unshift.apply(d,u),d.push.apply(d,f),l=d.length,c=Promise.resolve(t);p<l;)c=c.then(d[p++],d[p++]);return c}l=u.length;for(var h=t;p<l;){var v=u[p++],y=u[p++];try{h=v(h);}catch(e){y.call(this,e);break}}try{c=jt.call(this,h);}catch(e){return Promise.reject(e)}for(p=0,l=f.length;p<l;)c=c.then(f[p++],f[p++]);return c}},{key:"getUri",value:function(e){return ke(nt((e=it(this.defaults,e)).baseURL,e.url,e.allowAbsoluteUrls),e.params,e.paramsSerializer)}}]),e}();de.forEach(["delete","get","head","options"],(function(e){_t.prototype[e]=function(t,r){return this.request(it(r||{},{method:e,url:t,data:(r||{}).data}))};})),de.forEach(["post","put","patch"],(function(e){function t(t){return function(r,n,o){return this.request(it(o||{},{method:e,headers:t?{"Content-Type":"multipart/form-data"}:{},url:r,data:n}))}}_t.prototype[e]=t(),_t.prototype[e+"Form"]=t(!0);}));var Ut=_t,Ft=function(){function e(t){if(h(this,e),"function"!=typeof t)throw new TypeError("executor must be a function.");var r;this.promise=new Promise((function(e){r=e;}));var n=this;this.promise.then((function(e){if(n._listeners){for(var t=n._listeners.length;t-- >0;)n._listeners[t](e);n._listeners=null;}})),this.promise.then=function(e){var t,r=new Promise((function(e){n.subscribe(e),t=e;})).then(e);return r.cancel=function(){n.unsubscribe(t);},r},t((function(e,t,o){n.reason||(n.reason=new Ge(e,t,o),r(n.reason));}));}return y(e,[{key:"throwIfRequested",value:function(){if(this.reason)throw this.reason}},{key:"subscribe",value:function(e){this.reason?e(this.reason):this._listeners?this._listeners.push(e):this._listeners=[e];}},{key:"unsubscribe",value:function(e){if(this._listeners){var t=this._listeners.indexOf(e);-1!==t&&this._listeners.splice(t,1);}}},{key:"toAbortSignal",value:function(){var e=this,t=new AbortController,r=function(e){t.abort(e);};return this.subscribe(r),t.signal.unsubscribe=function(){return e.unsubscribe(r)},t.signal}}],[{key:"source",value:function(){var t;return {token:new e((function(e){t=e;})),cancel:t}}}]),e}(),Bt=Ft;var Dt={Continue:100,SwitchingProtocols:101,Processing:102,EarlyHints:103,Ok:200,Created:201,Accepted:202,NonAuthoritativeInformation:203,NoContent:204,ResetContent:205,PartialContent:206,MultiStatus:207,AlreadyReported:208,ImUsed:226,MultipleChoices:300,MovedPermanently:301,Found:302,SeeOther:303,NotModified:304,UseProxy:305,Unused:306,TemporaryRedirect:307,PermanentRedirect:308,BadRequest:400,Unauthorized:401,PaymentRequired:402,Forbidden:403,NotFound:404,MethodNotAllowed:405,NotAcceptable:406,ProxyAuthenticationRequired:407,RequestTimeout:408,Conflict:409,Gone:410,LengthRequired:411,PreconditionFailed:412,PayloadTooLarge:413,UriTooLong:414,UnsupportedMediaType:415,RangeNotSatisfiable:416,ExpectationFailed:417,ImATeapot:418,MisdirectedRequest:421,UnprocessableEntity:422,Locked:423,FailedDependency:424,TooEarly:425,UpgradeRequired:426,PreconditionRequired:428,TooManyRequests:429,RequestHeaderFieldsTooLarge:431,UnavailableForLegalReasons:451,InternalServerError:500,NotImplemented:501,BadGateway:502,ServiceUnavailable:503,GatewayTimeout:504,HttpVersionNotSupported:505,VariantAlsoNegotiates:506,InsufficientStorage:507,LoopDetected:508,NotExtended:510,NetworkAuthenticationRequired:511,WebServerIsDown:521,ConnectionTimedOut:522,OriginIsUnreachable:523,TimeoutOccurred:524,SslHandshakeFailed:525,InvalidSslCertificate:526};Object.entries(Dt).forEach((function(e){var t=b(e,2),r=t[0],n=t[1];Dt[n]=r;}));var It=Dt;var qt=function e(t){var r=new Ut(t),n=O(Ut.prototype.request,r);return de.extend(n,Ut.prototype,r,{allOwnKeys:!0}),de.extend(n,r,null,{allOwnKeys:!0}),n.create=function(r){return e(it(t,r))},n}(De);return qt.Axios=Ut,qt.CanceledError=Ge,qt.CancelToken=Bt,qt.isCancel=Ve,qt.VERSION=At,qt.toFormData=Ee,qt.AxiosError=he,qt.Cancel=qt.CanceledError,qt.all=function(e){return Promise.all(e)},qt.spread=function(e){return function(t){return e.apply(null,t)}},qt.isAxiosError=function(e){return de.isObject(e)&&!0===e.isAxiosError},qt.mergeConfig=it,qt.AxiosHeaders=We,qt.formToJSON=function(e){return Fe(de.isHTMLForm(e)?new FormData(e):e)},qt.getAdapter=kt.getAdapter,qt.HttpStatusCode=It,qt.default=qt,qt}));





var axios = module.exports;

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const exports = {};
Object.defineProperty(exports, '__esModule', { value: true });

const matchName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const iconDefaults = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16,
  rotate: 0,
  vFlip: false,
  hFlip: false
});
function fullIcon(data) {
  return { ...iconDefaults, ...data };
}

const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIcon(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIcon(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIcon(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIcon = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchName)) && icon.name.match(matchName));
};

function mergeIconData(icon, alias) {
  const result = { ...icon };
  for (const key in iconDefaults) {
    const prop = key;
    if (alias[prop] !== void 0) {
      const value = alias[prop];
      if (result[prop] === void 0) {
        result[prop] = value;
        continue;
      }
      switch (prop) {
        case "rotate":
          result[prop] = (result[prop] + value) % 4;
          break;
        case "hFlip":
        case "vFlip":
          result[prop] = value !== result[prop];
          break;
        default:
          result[prop] = value;
      }
    }
  }
  return result;
}

function getIconData$1(data, name, full = false) {
  function getIcon(name2, iteration) {
    if (data.icons[name2] !== void 0) {
      return Object.assign({}, data.icons[name2]);
    }
    if (iteration > 5) {
      return null;
    }
    const aliases = data.aliases;
    if (aliases && aliases[name2] !== void 0) {
      const item = aliases[name2];
      const result2 = getIcon(item.parent, iteration + 1);
      if (result2) {
        return mergeIconData(result2, item);
      }
      return result2;
    }
    const chars = data.chars;
    if (!iteration && chars && chars[name2] !== void 0) {
      return getIcon(chars[name2], iteration + 1);
    }
    return null;
  }
  const result = getIcon(name, 0);
  if (result) {
    for (const key in iconDefaults) {
      if (result[key] === void 0 && data[key] !== void 0) {
        result[key] = data[key];
      }
    }
  }
  return result && full ? fullIcon(result) : result;
}

function isVariation(item) {
  for (const key in iconDefaults) {
    if (item[key] !== void 0) {
      return true;
    }
  }
  return false;
}
function parseIconSet(data, callback, options) {
  options = options || {};
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const icons = data.icons;
  Object.keys(icons).forEach((name) => {
    const iconData = getIconData$1(data, name, true);
    if (iconData) {
      callback(name, iconData);
      names.push(name);
    }
  });
  const parseAliases = options.aliases || "all";
  if (parseAliases !== "none" && typeof data.aliases === "object") {
    const aliases = data.aliases;
    Object.keys(aliases).forEach((name) => {
      if (parseAliases === "variations" && isVariation(aliases[name])) {
        return;
      }
      const iconData = getIconData$1(data, name, true);
      if (iconData) {
        callback(name, iconData);
        names.push(name);
      }
    });
  }
  return names;
}

const optionalProperties = {
  provider: "string",
  aliases: "object",
  not_found: "object"
};
for (const prop in iconDefaults) {
  optionalProperties[prop] = typeof iconDefaults[prop];
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  for (const prop in optionalProperties) {
    if (obj[prop] !== void 0 && typeof obj[prop] !== optionalProperties[prop]) {
      return null;
    }
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchName) || typeof icon.body !== "string") {
      return null;
    }
    for (const prop in iconDefaults) {
      if (icon[prop] !== void 0 && typeof icon[prop] !== typeof iconDefaults[prop]) {
        return null;
      }
    }
  }
  const aliases = data.aliases;
  if (aliases) {
    for (const name in aliases) {
      const icon = aliases[name];
      const parent = icon.parent;
      if (!name.match(matchName) || typeof parent !== "string" || !icons[parent] && !aliases[parent]) {
        return null;
      }
      for (const prop in iconDefaults) {
        if (icon[prop] !== void 0 && typeof icon[prop] !== typeof iconDefaults[prop]) {
          return null;
        }
      }
    }
  }
  return data;
}

const storageVersion = 1;
let storage$1 = /* @__PURE__ */ Object.create(null);
try {
  const w = window || self;
  if (w && w._iconifyStorage.version === storageVersion) {
    storage$1 = w._iconifyStorage.storage;
  }
} catch (err) {
}
function shareStorage() {
  try {
    const w = window || self;
    if (w && !w._iconifyStorage) {
      w._iconifyStorage = {
        version: storageVersion,
        storage: storage$1
      };
    }
  } catch (err) {
  }
}
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ Object.create(null)
  };
}
function getStorage(provider, prefix) {
  if (storage$1[provider] === void 0) {
    storage$1[provider] = /* @__PURE__ */ Object.create(null);
  }
  const providerStorage = storage$1[provider];
  if (providerStorage[prefix] === void 0) {
    providerStorage[prefix] = newStorage(provider, prefix);
  }
  return providerStorage[prefix];
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  const t = Date.now();
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing[name] = t;
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = Object.freeze(fullIcon(icon));
      return true;
    }
  } catch (err) {
  }
  return false;
}
function getIconFromStorage(storage2, name) {
  const value = storage2.icons[name];
  return value === void 0 ? null : value;
}
function listIcons(provider, prefix) {
  let allIcons = [];
  let providers;
  if (typeof provider === "string") {
    providers = [provider];
  } else {
    providers = Object.keys(storage$1);
  }
  providers.forEach((provider2) => {
    let prefixes;
    if (typeof provider2 === "string" && typeof prefix === "string") {
      prefixes = [prefix];
    } else {
      prefixes = storage$1[provider2] === void 0 ? [] : Object.keys(storage$1[provider2]);
    }
    prefixes.forEach((prefix2) => {
      const storage2 = getStorage(provider2, prefix2);
      const icons = Object.keys(storage2.icons).map((name) => (provider2 !== "" ? "@" + provider2 + ":" : "") + prefix2 + ":" + name);
      allIcons = allIcons.concat(icons);
    });
  });
  return allIcons;
}

let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  return icon ? getIconFromStorage(getStorage(icon.provider, icon.prefix), icon.name) : null;
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = typeof data.provider === "string" ? data.provider : "";
  }
  if (simpleNames && provider === "" && (typeof data.prefix !== "string" || data.prefix === "")) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  if (typeof data.prefix !== "string" || !validateIcon({
    provider,
    prefix: data.prefix,
    name: "a"
  })) {
    return false;
  }
  const storage = getStorage(provider, data.prefix);
  return !!addIconSet(storage, data);
}
function iconExists(name) {
  return getIconData(name) !== null;
}
function getIcon(name) {
  const result = getIconData(name);
  return result ? { ...result } : null;
}

const defaults = Object.freeze({
  inline: false,
  width: null,
  height: null,
  hAlign: "center",
  vAlign: "middle",
  slice: false,
  hFlip: false,
  vFlip: false,
  rotate: 0
});
function mergeCustomisations(defaults2, item) {
  const result = {};
  for (const key in defaults2) {
    const attr = key;
    result[attr] = defaults2[attr];
    if (item[attr] === void 0) {
      continue;
    }
    const value = item[attr];
    switch (attr) {
      case "inline":
      case "slice":
        if (typeof value === "boolean") {
          result[attr] = value;
        }
        break;
      case "hFlip":
      case "vFlip":
        if (value === true) {
          result[attr] = !result[attr];
        }
        break;
      case "hAlign":
      case "vAlign":
        if (typeof value === "string" && value !== "") {
          result[attr] = value;
        }
        break;
      case "width":
      case "height":
        if (typeof value === "string" && value !== "" || typeof value === "number" && value || value === null) {
          result[attr] = value;
        }
        break;
      case "rotate":
        if (typeof value === "number") {
          result[attr] += value;
        }
        break;
    }
  }
  return result;
}

const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision === void 0 ? 100 : precision;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}

function preserveAspectRatio(props) {
  let result = "";
  switch (props.hAlign) {
    case "left":
      result += "xMin";
      break;
    case "right":
      result += "xMax";
      break;
    default:
      result += "xMid";
  }
  switch (props.vAlign) {
    case "top":
      result += "YMin";
      break;
    case "bottom":
      result += "YMax";
      break;
    default:
      result += "YMid";
  }
  result += props.slice ? " slice" : " meet";
  return result;
}
function iconToSVG(icon, customisations) {
  const box = {
    left: icon.left,
    top: icon.top,
    width: icon.width,
    height: icon.height
  };
  let body = icon.body;
  [icon, customisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== 0 || box.top !== 0) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  let width, height;
  if (customisations.width === null && customisations.height === null) {
    height = "1em";
    width = calculateSize(height, box.width / box.height);
  } else if (customisations.width !== null && customisations.height !== null) {
    width = customisations.width;
    height = customisations.height;
  } else if (customisations.height !== null) {
    height = customisations.height;
    width = calculateSize(height, box.width / box.height);
  } else {
    width = customisations.width;
    height = calculateSize(width, box.height / box.width);
  }
  if (width === "auto") {
    width = box.width;
  }
  if (height === "auto") {
    height = box.height;
  }
  width = typeof width === "string" ? width : width.toString() + "";
  height = typeof height === "string" ? height : height.toString() + "";
  const result = {
    attributes: {
      width,
      height,
      preserveAspectRatio: preserveAspectRatio(customisations),
      viewBox: box.left.toString() + " " + box.top.toString() + " " + box.width.toString() + " " + box.height.toString()
    },
    body
  };
  if (customisations.inline) {
    result.inline = true;
  }
  return result;
}

function buildIcon(icon, customisations) {
  return iconToSVG(fullIcon(icon), customisations ? mergeCustomisations(defaults, customisations) : defaults);
}

const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + "$3");
  });
  return body;
}

const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}

function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path === void 0 ? "/" : source.path,
    maxURL: source.maxURL ? source.maxURL : 500,
    rotate: source.rotate ? source.rotate : 750,
    timeout: source.timeout ? source.timeout : 5e3,
    random: source.random === true,
    index: source.index ? source.index : 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
function listAPIProviders() {
  return Object.keys(configStorage);
}

const mergeParams = (base, params) => {
  let result = base, hasParams = result.indexOf("?") !== -1;
  function paramToString(value) {
    switch (typeof value) {
      case "boolean":
        return value ? "true" : "false";
      case "number":
        return encodeURIComponent(value);
      case "string":
        return encodeURIComponent(value);
      default:
        throw new Error("Invalid parameter");
    }
  }
  Object.keys(params).forEach((key) => {
    let value;
    try {
      value = paramToString(params[key]);
    } catch (err) {
      return;
    }
    result += (hasParams ? "&" : "?") + encodeURIComponent(key) + "=" + value;
    hasParams = true;
  });
  return result;
};

const maxLengthCache = {};
const pathCache = {};
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
  return null;
};
let fetchModule = detectFetch();
function setFetch(fetch2) {
  fetchModule = fetch2;
}
function getFetch() {
  return fetchModule;
}
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = mergeParams(prefix + ".json", {
      icons: ""
    });
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  const cacheKey = provider + ":" + prefix;
  pathCache[provider] = config.path;
  maxLengthCache[cacheKey] = result;
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  let maxLength = maxLengthCache[prefix];
  if (maxLength === void 0) {
    maxLength = calculateMaxLength(provider, prefix);
  }
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    if (pathCache[provider] === void 0) {
      const config = getAPIConfig(provider);
      if (!config) {
        return "/";
      }
      pathCache[provider] = config.path;
    }
    return pathCache[provider];
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      path += mergeParams(prefix + ".json", {
        icons: iconsList
      });
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        callback("next", defaultError);
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};

function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    if (storage[provider] === void 0) {
      storage[provider] = /* @__PURE__ */ Object.create(null);
    }
    const providerStorage = storage[provider];
    if (providerStorage[prefix] === void 0) {
      providerStorage[prefix] = getStorage(provider, prefix);
    }
    const localStorage = providerStorage[prefix];
    let list;
    if (localStorage.icons[name] !== void 0) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing[name] !== void 0) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}

const callbacks = /* @__PURE__ */ Object.create(null);
const pendingUpdates = /* @__PURE__ */ Object.create(null);
function removeCallback(sources, id) {
  sources.forEach((source) => {
    const provider = source.provider;
    if (callbacks[provider] === void 0) {
      return;
    }
    const providerCallbacks = callbacks[provider];
    const prefix = source.prefix;
    const items = providerCallbacks[prefix];
    if (items) {
      providerCallbacks[prefix] = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(provider, prefix) {
  if (pendingUpdates[provider] === void 0) {
    pendingUpdates[provider] = /* @__PURE__ */ Object.create(null);
  }
  const providerPendingUpdates = pendingUpdates[provider];
  if (!providerPendingUpdates[prefix]) {
    providerPendingUpdates[prefix] = true;
    setTimeout(() => {
      providerPendingUpdates[prefix] = false;
      if (callbacks[provider] === void 0 || callbacks[provider][prefix] === void 0) {
        return;
      }
      const items = callbacks[provider][prefix].slice(0);
      if (!items.length) {
        return;
      }
      const storage = getStorage(provider, prefix);
      let hasPending = false;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage.icons[name] !== void 0) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage.missing[name] !== void 0) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([
              {
                provider,
                prefix
              }
            ], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((source) => {
    const provider = source.provider;
    const prefix = source.prefix;
    if (callbacks[provider] === void 0) {
      callbacks[provider] = /* @__PURE__ */ Object.create(null);
    }
    const providerCallbacks = callbacks[provider];
    if (providerCallbacks[prefix] === void 0) {
      providerCallbacks[prefix] = [];
    }
    providerCallbacks[prefix].push(item);
  });
  return abort;
}

function listToIcons(list, validate = true, simpleNames = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, false, simpleNames) : item;
    if (!validate || validateIcon(icon, simpleNames)) {
      result.push({
        provider: icon.provider,
        prefix: icon.prefix,
        name: icon.name
      });
    }
  });
  return result;
}

// src/config.ts
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};

// src/query.ts
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}

// src/index.ts
function setConfig(config) {
  if (typeof config !== "object" || typeof config.resources !== "object" || !(config.resources instanceof Array) || !config.resources.length) {
    throw new Error("Invalid Reduncancy configuration");
  }
  const newConfig = /* @__PURE__ */ Object.create(null);
  let key;
  for (key in defaultConfig) {
    if (config[key] !== void 0) {
      newConfig[key] = config[key];
    } else {
      newConfig[key] = defaultConfig[key];
    }
  }
  return newConfig;
}
function initRedundancy(cfg) {
  const config = setConfig(cfg);
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    const result = queries.find((value) => {
      return callback(value);
    });
    return result !== void 0 ? result : null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}

function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (redundancyCache[provider] === void 0) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send = api.send;
      }
    }
  }
  if (!redundancy || !send) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send, callback)().abort;
}

const cache = {};

function emptyCallback() {
}
const pendingIcons = /* @__PURE__ */ Object.create(null);
const iconsToLoad = /* @__PURE__ */ Object.create(null);
const loaderFlags = /* @__PURE__ */ Object.create(null);
const queueFlags = /* @__PURE__ */ Object.create(null);
function loadedNewIcons(provider, prefix) {
  if (loaderFlags[provider] === void 0) {
    loaderFlags[provider] = /* @__PURE__ */ Object.create(null);
  }
  const providerLoaderFlags = loaderFlags[provider];
  if (!providerLoaderFlags[prefix]) {
    providerLoaderFlags[prefix] = true;
    setTimeout(() => {
      providerLoaderFlags[prefix] = false;
      updateCallbacks(provider, prefix);
    });
  }
}
const errorsCache = /* @__PURE__ */ Object.create(null);
function loadNewIcons(provider, prefix, icons) {
  function err() {
    const key = (provider === "" ? "" : "@" + provider + ":") + prefix;
    const time = Math.floor(Date.now() / 6e4);
    if (errorsCache[key] < time) {
      errorsCache[key] = time;
      console.error('Unable to retrieve icons for "' + key + '" because API is not configured properly.');
    }
  }
  if (iconsToLoad[provider] === void 0) {
    iconsToLoad[provider] = /* @__PURE__ */ Object.create(null);
  }
  const providerIconsToLoad = iconsToLoad[provider];
  if (queueFlags[provider] === void 0) {
    queueFlags[provider] = /* @__PURE__ */ Object.create(null);
  }
  const providerQueueFlags = queueFlags[provider];
  if (pendingIcons[provider] === void 0) {
    pendingIcons[provider] = /* @__PURE__ */ Object.create(null);
  }
  const providerPendingIcons = pendingIcons[provider];
  if (providerIconsToLoad[prefix] === void 0) {
    providerIconsToLoad[prefix] = icons;
  } else {
    providerIconsToLoad[prefix] = providerIconsToLoad[prefix].concat(icons).sort();
  }
  if (!providerQueueFlags[prefix]) {
    providerQueueFlags[prefix] = true;
    setTimeout(() => {
      providerQueueFlags[prefix] = false;
      const icons2 = providerIconsToLoad[prefix];
      delete providerIconsToLoad[prefix];
      const api = getAPIModule(provider);
      if (!api) {
        err();
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data, error) => {
          const storage = getStorage(provider, prefix);
          if (typeof data !== "object") {
            if (error !== 404) {
              return;
            }
            const t = Date.now();
            item.icons.forEach((name) => {
              storage.missing[name] = t;
            });
          } else {
            try {
              const parsed = addIconSet(storage, data);
              if (!parsed.length) {
                return;
              }
              const pending = providerPendingIcons[prefix];
              parsed.forEach((name) => {
                delete pending[name];
              });
              if (cache.store) {
                cache.store(provider, data);
              }
            } catch (err2) {
              console.error(err2);
            }
          }
          loadedNewIcons(provider, prefix);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const provider = icon.provider;
    const prefix = icon.prefix;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push({
      provider,
      prefix
    });
    if (pendingIcons[provider] === void 0) {
      pendingIcons[provider] = /* @__PURE__ */ Object.create(null);
    }
    const providerPendingIcons = pendingIcons[provider];
    if (providerPendingIcons[prefix] === void 0) {
      providerPendingIcons[prefix] = /* @__PURE__ */ Object.create(null);
    }
    if (newIcons[provider] === void 0) {
      newIcons[provider] = /* @__PURE__ */ Object.create(null);
    }
    const providerNewIcons = newIcons[provider];
    if (providerNewIcons[prefix] === void 0) {
      providerNewIcons[prefix] = [];
    }
  });
  const time = Date.now();
  sortedIcons.pending.forEach((icon) => {
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const pendingQueue = pendingIcons[provider][prefix];
    if (pendingQueue[name] === void 0) {
      pendingQueue[name] = time;
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((source) => {
    const provider = source.provider;
    const prefix = source.prefix;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(provider, prefix, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
const loadIcon = (icon) => {
  return new Promise((fulfill, reject) => {
    const iconObj = typeof icon === "string" ? stringToIcon(icon) : icon;
    loadIcons([iconObj || icon], (loaded) => {
      if (loaded.length && iconObj) {
        const storage = getStorage(iconObj.provider, iconObj.prefix);
        const data = getIconFromStorage(storage, iconObj.name);
        if (data) {
          fulfill(data);
          return;
        }
      }
      reject(icon);
    });
  });
};

const cacheVersion = "iconify2";
const cachePrefix = "iconify";
const countKey = cachePrefix + "-count";
const versionKey = cachePrefix + "-version";
const hour = 36e5;
const cacheExpiration = 168;
const config = {
  local: true,
  session: true
};
let loaded = false;
const count = {
  local: 0,
  session: 0
};
const emptyList = {
  local: [],
  session: []
};
let _window = typeof window === "undefined" ? {} : window;
function getGlobal(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  config[key] = false;
  return null;
}
function setCount(storage, key, value) {
  try {
    storage.setItem(countKey, value.toString());
    count[key] = value;
    return true;
  } catch (err) {
    return false;
  }
}
function getCount(storage) {
  const count2 = storage.getItem(countKey);
  if (count2) {
    const total = parseInt(count2);
    return total ? total : 0;
  }
  return 0;
}
function initCache(storage, key) {
  try {
    storage.setItem(versionKey, cacheVersion);
  } catch (err) {
  }
  setCount(storage, key, 0);
}
function destroyCache(storage) {
  try {
    const total = getCount(storage);
    for (let i = 0; i < total; i++) {
      storage.removeItem(cachePrefix + i.toString());
    }
  } catch (err) {
  }
}
const loadCache = () => {
  if (loaded) {
    return;
  }
  loaded = true;
  const minTime = Math.floor(Date.now() / hour) - cacheExpiration;
  function load(key) {
    const func = getGlobal(key);
    if (!func) {
      return;
    }
    const getItem = (index) => {
      const name = cachePrefix + index.toString();
      const item = func.getItem(name);
      if (typeof item !== "string") {
        return false;
      }
      let valid = true;
      try {
        const data = JSON.parse(item);
        if (typeof data !== "object" || typeof data.cached !== "number" || data.cached < minTime || typeof data.provider !== "string" || typeof data.data !== "object" || typeof data.data.prefix !== "string") {
          valid = false;
        } else {
          const provider = data.provider;
          const prefix = data.data.prefix;
          const storage = getStorage(provider, prefix);
          valid = addIconSet(storage, data.data).length > 0;
        }
      } catch (err) {
        valid = false;
      }
      if (!valid) {
        func.removeItem(name);
      }
      return valid;
    };
    try {
      const version = func.getItem(versionKey);
      if (version !== cacheVersion) {
        if (version) {
          destroyCache(func);
        }
        initCache(func, key);
        return;
      }
      let total = getCount(func);
      for (let i = total - 1; i >= 0; i--) {
        if (!getItem(i)) {
          if (i === total - 1) {
            total--;
          } else {
            emptyList[key].push(i);
          }
        }
      }
      setCount(func, key, total);
    } catch (err) {
    }
  }
  for (const key in config) {
    load(key);
  }
};
const storeCache = (provider, data) => {
  if (!loaded) {
    loadCache();
  }
  function store(key) {
    if (!config[key]) {
      return false;
    }
    const func = getGlobal(key);
    if (!func) {
      return false;
    }
    let index = emptyList[key].shift();
    if (index === void 0) {
      index = count[key];
      if (!setCount(func, key, index + 1)) {
        return false;
      }
    }
    try {
      const item = {
        cached: Math.floor(Date.now() / hour),
        provider,
        data
      };
      func.setItem(cachePrefix + index.toString(), JSON.stringify(item));
    } catch (err) {
      return false;
    }
    return true;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
};

function toggleBrowserCache(storage, value) {
  switch (storage) {
    case "local":
    case "session":
      config[storage] = value;
      break;
    case "all":
      for (const key in config) {
        config[key] = value;
      }
      break;
  }
}

const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function alignmentFromString(custom, align) {
  align.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "left":
      case "center":
      case "right":
        custom.hAlign = value;
        break;
      case "top":
      case "middle":
      case "bottom":
        custom.vAlign = value;
        break;
      case "slice":
      case "crop":
        custom.slice = true;
        break;
      case "meet":
        custom.slice = false;
    }
  });
}

function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}

/**
 * Default SVG attributes
 */
const svgDefaults = {
    'xmlns': 'http://www.w3.org/2000/svg',
    'xmlns:xlink': 'http://www.w3.org/1999/xlink',
    'aria-hidden': true,
    'role': 'img',
};
/**
 * Generate icon from properties
 */
function render(
// Icon must be validated before calling this function
icon, 
// Properties
props) {
    const customisations = mergeCustomisations(defaults, props);
    const componentProps = { ...svgDefaults };
    // Create style if missing
    let style = typeof props.style === 'string' ? props.style : '';
    // Get element properties
    for (let key in props) {
        const value = props[key];
        if (value === void 0) {
            continue;
        }
        switch (key) {
            // Properties to ignore
            case 'icon':
            case 'style':
            case 'onLoad':
                break;
            // Boolean attributes
            case 'inline':
            case 'hFlip':
            case 'vFlip':
                customisations[key] =
                    value === true || value === 'true' || value === 1;
                break;
            // Flip as string: 'horizontal,vertical'
            case 'flip':
                if (typeof value === 'string') {
                    flipFromString(customisations, value);
                }
                break;
            // Alignment as string
            case 'align':
                if (typeof value === 'string') {
                    alignmentFromString(customisations, value);
                }
                break;
            // Color: copy to style, add extra ';' in case style is missing it
            case 'color':
                style =
                    style +
                        (style.length > 0 && style.trim().slice(-1) !== ';'
                            ? ';'
                            : '') +
                        'color: ' +
                        value +
                        '; ';
                break;
            // Rotation as string
            case 'rotate':
                if (typeof value === 'string') {
                    customisations[key] = rotateFromString(value);
                }
                else if (typeof value === 'number') {
                    customisations[key] = value;
                }
                break;
            // Remove aria-hidden
            case 'ariaHidden':
            case 'aria-hidden':
                if (value !== true && value !== 'true') {
                    delete componentProps['aria-hidden'];
                }
                break;
            default:
                if (key.slice(0, 3) === 'on:') {
                    // Svelte event
                    break;
                }
                // Copy missing property if it does not exist in customisations
                if (defaults[key] === void 0) {
                    componentProps[key] = value;
                }
        }
    }
    // Generate icon
    const item = iconToSVG(icon, customisations);
    // Add icon stuff
    for (let key in item.attributes) {
        componentProps[key] =
            item.attributes[key];
    }
    if (item.inline) {
        // Style overrides it
        style = 'vertical-align: -0.125em; ' + style;
    }
    // Style
    if (style !== '') {
        componentProps.style = style;
    }
    // Counter for ids based on "id" property to render icons consistently on server and client
    let localCounter = 0;
    let id = props.id;
    if (typeof id === 'string') {
        // Convert '-' to '_' to avoid errors in animations
        id = id.replace(/-/g, '_');
    }
    // Generate HTML
    return {
        attributes: componentProps,
        body: replaceIDs(item.body, id ? () => id + 'ID' + localCounter++ : 'iconifySvelte'),
    };
}

/**
 * Enable cache
 */
function enableCache(storage) {
    toggleBrowserCache(storage, true);
}
/**
 * Disable cache
 */
function disableCache(storage) {
    toggleBrowserCache(storage, false);
}
/**
 * Initialise stuff
 */
// Enable short names
allowSimpleNames(true);
// Set API module
setAPIModule('', fetchAPIModule);
/**
 * Browser stuff
 */
if (typeof document !== 'undefined' && typeof window !== 'undefined') {
    // Set cache and load existing cache
    cache.store = storeCache;
    loadCache();
    const _window = window;
    // Load icons from global "IconifyPreload"
    if (_window.IconifyPreload !== void 0) {
        const preload = _window.IconifyPreload;
        const err = 'Invalid IconifyPreload syntax.';
        if (typeof preload === 'object' && preload !== null) {
            (preload instanceof Array ? preload : [preload]).forEach((item) => {
                try {
                    if (
                    // Check if item is an object and not null/array
                    typeof item !== 'object' ||
                        item === null ||
                        item instanceof Array ||
                        // Check for 'icons' and 'prefix'
                        typeof item.icons !== 'object' ||
                        typeof item.prefix !== 'string' ||
                        // Add icon set
                        !addCollection(item)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            });
        }
    }
    // Set API from global "IconifyProviders"
    if (_window.IconifyProviders !== void 0) {
        const providers = _window.IconifyProviders;
        if (typeof providers === 'object' && providers !== null) {
            for (let key in providers) {
                const err = 'IconifyProviders[' + key + '] is invalid.';
                try {
                    const value = providers[key];
                    if (typeof value !== 'object' ||
                        !value ||
                        value.resources === void 0) {
                        continue;
                    }
                    if (!addAPIProvider(key, value)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            }
        }
    }
}
/**
 * Check if component needs to be updated
 */
function checkIconState(icon, state, mounted, callback, onload) {
    // Abort loading icon
    function abortLoading() {
        if (state.loading) {
            state.loading.abort();
            state.loading = null;
        }
    }
    // Icon is an object
    if (typeof icon === 'object' &&
        icon !== null &&
        typeof icon.body === 'string') {
        // Stop loading
        state.name = '';
        abortLoading();
        return { data: fullIcon(icon) };
    }
    // Invalid icon?
    let iconName;
    if (typeof icon !== 'string' ||
        (iconName = stringToIcon(icon, false, true)) === null) {
        abortLoading();
        return null;
    }
    // Load icon
    const data = getIconData(iconName);
    if (data === null) {
        // Icon needs to be loaded
        // Do not load icon until component is mounted
        if (mounted && (!state.loading || state.loading.name !== icon)) {
            // New icon to load
            abortLoading();
            state.name = '';
            state.loading = {
                name: icon,
                abort: loadIcons([iconName], callback),
            };
        }
        return null;
    }
    // Icon data is available
    abortLoading();
    if (state.name !== icon) {
        state.name = icon;
        if (onload && !state.destroyed) {
            onload(icon);
        }
    }
    // Add classes
    const classes = ['iconify'];
    if (iconName.prefix !== '') {
        classes.push('iconify--' + iconName.prefix);
    }
    if (iconName.provider !== '') {
        classes.push('iconify--' + iconName.provider);
    }
    return { data, classes };
}
/**
 * Generate icon
 */
function generateIcon(icon, props) {
    return icon ? render(icon, props) : null;
}
/**
 * Internal API
 */
const _api = {
    getAPIConfig,
    setAPIModule,
    sendAPIQuery,
    setFetch,
    getFetch,
    listAPIProviders,
    mergeParams,
};

exports._api = _api;
exports.addAPIProvider = addAPIProvider;
exports.addCollection = addCollection;
exports.addIcon = addIcon;
exports.buildIcon = buildIcon;
exports.calculateSize = calculateSize;
exports.checkIconState = checkIconState;
exports.disableCache = disableCache;
exports.enableCache = enableCache;
exports.generateIcon = generateIcon;
exports.getIcon = getIcon;
exports.iconExists = iconExists;
exports.listIcons = listIcons;
exports.loadIcon = loadIcon;
exports.loadIcons = loadIcons;
exports.replaceIDs = replaceIDs;
exports.shareStorage = shareStorage;

/* generated by Svelte v3.59.1 */

function create_if_block$1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] !== null && create_if_block$1(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0] !== null) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		{
			const iconData = checkIconState($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_if_block_5(ctx) {
	let div;
	let t_value = /*form*/ ctx[0].error_message + "";
	let t;
	let div_intro;

	return {
		c() {
			div = element("div");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "message error svelte-1n6lyan");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 1 && t_value !== (t_value = /*form*/ ctx[0].error_message + "")) set_data(t, t_value);
		},
		i(local) {
			if (!div_intro) {
				add_render_callback(() => {
					div_intro = create_in_transition(div, fade, {});
					div_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (184:22) 
function create_if_block_4(ctx) {
	let div;
	let t_value = /*form*/ ctx[0].success_message + "";
	let t;
	let div_intro;

	return {
		c() {
			div = element("div");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "message svelte-1n6lyan");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 1 && t_value !== (t_value = /*form*/ ctx[0].success_message + "")) set_data(t, t_value);
		},
		i(local) {
			if (!div_intro) {
				add_render_callback(() => {
					div_intro = create_in_transition(div, fade, {});
					div_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (167:2) {#if !submitted && !error}
function create_if_block_2(ctx) {
	let form_1;
	let label;
	let input;
	let input_placeholder_value;
	let t;
	let button;
	let current_block_type_index;
	let if_block;
	let current;
	let mounted;
	let dispose;
	const if_block_creators = [create_if_block_3, create_else_block];
	const if_blocks = [];

	function select_block_type_1(ctx, dirty) {
		if (!/*submitting*/ ctx[3]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type_1(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			form_1 = element("form");
			label = element("label");
			input = element("input");
			t = space();
			button = element("button");
			if_block.c();
			this.h();
		},
		l(nodes) {
			form_1 = claim_element(nodes, "FORM", { class: true });
			var form_1_nodes = children(form_1);
			label = claim_element(form_1_nodes, "LABEL", { class: true });
			var label_nodes = children(label);

			input = claim_element(label_nodes, "INPUT", {
				name: true,
				type: true,
				placeholder: true,
				class: true
			});

			label_nodes.forEach(detach);
			t = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { class: true, type: true });
			var button_nodes = children(button);
			if_block.l(button_nodes);
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			input.required = true;
			attr(input, "name", "email");
			attr(input, "type", "text");
			attr(input, "placeholder", input_placeholder_value = /*form*/ ctx[0].placeholder);
			attr(input, "class", "svelte-1n6lyan");
			attr(label, "class", "svelte-1n6lyan");
			attr(button, "class", "button svelte-1n6lyan");
			attr(button, "type", "submit");
			attr(form_1, "class", "svelte-1n6lyan");
		},
		m(target, anchor) {
			insert_hydration(target, form_1, anchor);
			append_hydration(form_1, label);
			append_hydration(label, input);
			append_hydration(form_1, t);
			append_hydration(form_1, button);
			if_blocks[current_block_type_index].m(button, null);
			current = true;

			if (!mounted) {
				dispose = listen(form_1, "submit", prevent_default(/*submit_form*/ ctx[6]));
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty & /*form*/ 1 && input_placeholder_value !== (input_placeholder_value = /*form*/ ctx[0].placeholder)) {
				attr(input, "placeholder", input_placeholder_value);
			}

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_1(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(button, null);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(form_1);
			if_blocks[current_block_type_index].d();
			mounted = false;
			dispose();
		}
	};
}

// (179:8) {:else}
function create_else_block(ctx) {
	let icon;
	let current;
	icon = new Component$1({ props: { icon: "eos-icons:loading" } });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (177:8) {#if !submitting}
function create_if_block_3(ctx) {
	let t_value = /*form*/ ctx[0].button_label + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*form*/ 1 && t_value !== (t_value = /*form*/ ctx[0].button_label + "")) set_data(t, t_value);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (189:2) {#if graphics.left}
function create_if_block_1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { class: true, src: true, alt: true });
			this.h();
		},
		h() {
			attr(img, "class", "graphic left svelte-1n6lyan");
			if (!src_url_equal(img.src, img_src_value = /*graphics*/ ctx[2].left.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*graphics*/ ctx[2].left.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*graphics*/ 4 && !src_url_equal(img.src, img_src_value = /*graphics*/ ctx[2].left.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*graphics*/ 4 && img_alt_value !== (img_alt_value = /*graphics*/ ctx[2].left.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (192:2) {#if graphics.right}
function create_if_block(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { class: true, src: true, alt: true });
			this.h();
		},
		h() {
			attr(img, "class", "graphic right svelte-1n6lyan");
			if (!src_url_equal(img.src, img_src_value = /*graphics*/ ctx[2].right.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*graphics*/ ctx[2].right.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*graphics*/ 4 && !src_url_equal(img.src, img_src_value = /*graphics*/ ctx[2].right.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*graphics*/ 4 && img_alt_value !== (img_alt_value = /*graphics*/ ctx[2].right.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let h1;
	let t0;
	let t1;
	let current_block_type_index;
	let if_block0;
	let t2;
	let t3;
	let current;
	const if_block_creators = [create_if_block_2, create_if_block_4, create_if_block_5];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (!/*submitted*/ ctx[4] && !/*error*/ ctx[5]) return 0;
		if (/*submitted*/ ctx[4]) return 1;
		if (/*error*/ ctx[5]) return 2;
		return -1;
	}

	if (~(current_block_type_index = select_block_type(ctx))) {
		if_block0 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	let if_block1 = /*graphics*/ ctx[2].left && create_if_block_1(ctx);
	let if_block2 = /*graphics*/ ctx[2].right && create_if_block(ctx);

	return {
		c() {
			section = element("section");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[1]);
			t1 = space();
			if (if_block0) if_block0.c();
			t2 = space();
			if (if_block1) if_block1.c();
			t3 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h1 = claim_element(section_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[1]);
			h1_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			if (if_block0) if_block0.l(section_nodes);
			t2 = claim_space(section_nodes);
			if (if_block1) if_block1.l(section_nodes);
			t3 = claim_space(section_nodes);
			if (if_block2) if_block2.l(section_nodes);
			section_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-1n6lyan");
			attr(section, "class", "section-container svelte-1n6lyan");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
			append_hydration(section, h1);
			append_hydration(h1, t0);
			append_hydration(section, t1);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(section, null);
			}

			append_hydration(section, t2);
			if (if_block1) if_block1.m(section, null);
			append_hydration(section, t3);
			if (if_block2) if_block2.m(section, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 2) set_data(t0, /*heading*/ ctx[1]);
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block0) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block0 = if_blocks[current_block_type_index];

					if (!if_block0) {
						if_block0 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block0.c();
					} else {
						if_block0.p(ctx, dirty);
					}

					transition_in(if_block0, 1);
					if_block0.m(section, t2);
				} else {
					if_block0 = null;
				}
			}

			if (/*graphics*/ ctx[2].left) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1(ctx);
					if_block1.c();
					if_block1.m(section, t3);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if (/*graphics*/ ctx[2].right) {
				if (if_block2) {
					if_block2.p(ctx, dirty);
				} else {
					if_block2 = create_if_block(ctx);
					if_block2.c();
					if_block2.m(section, null);
				}
			} else if (if_block2) {
				if_block2.d(1);
				if_block2 = null;
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block0);
			current = true;
		},
		o(local) {
			transition_out(if_block0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(section);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}

			if (if_block1) if_block1.d();
			if (if_block2) if_block2.d();
		}
	};
}

function get_form_data(form) {
	const form_data = new FormData(form);
	var object = {};

	form_data.forEach((value, key) => {
		object[key] = value;
	});

	return object;
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { form } = $$props;
	let { heading } = $$props;
	let { graphics } = $$props;
	let submitting = false;
	let submitted = false;
	let error = false;

	async function submit_form(e) {
		$$invalidate(3, submitting = true);
		const form_data = get_form_data(e.target);
		const { status } = await axios.post(form.endpoint, form_data).catch(e => ({ status: 400 }));

		if (status === 200) {
			$$invalidate(4, submitted = true);
		} else {
			$$invalidate(5, error = true);
		}
	}

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(7, props = $$props.props);
		if ('form' in $$props) $$invalidate(0, form = $$props.form);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('graphics' in $$props) $$invalidate(2, graphics = $$props.graphics);
	};

	return [form, heading, graphics, submitting, submitted, error, submit_form, props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			props: 7,
			form: 0,
			heading: 1,
			graphics: 2
		});
	}
}

export { Component as default };
