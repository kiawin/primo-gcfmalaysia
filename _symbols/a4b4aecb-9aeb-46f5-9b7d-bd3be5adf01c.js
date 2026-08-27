// Hero with form - Updated August 27, 2026
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

/*! Axios v1.20.0 Copyright (c) 2026 Matt Zabriskie and contributors */
!function(e,t){"object"==typeof exports$1&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):(e="undefined"!=typeof globalThis?globalThis:e||self).axios=t();}(undefined,function(){function e(e,t){this.v=e,this.k=t;}function t(e,t){(null==t||t>e.length)&&(t=e.length);for(var n=0,r=Array(t);n<t;n++)r[n]=e[n];return r}function n(t){var n={},r=!1;function o(n,o){return r=!0,o=new Promise(function(e){e(t[n](o));}),{done:!1,value:new e(o,1)}}return n["undefined"!=typeof Symbol&&Symbol.iterator||"@@iterator"]=function(){return this},n.next=function(e){return r?(r=!1,e):o("next",e)},"function"==typeof t.throw&&(n.throw=function(e){if(r)throw r=!1,e;return o("throw",e)}),"function"==typeof t.return&&(n.return=function(e){return r?(r=!1,e):o("return",e)}),n}function r(e){var t,n,r,i=2;for("undefined"!=typeof Symbol&&(n=Symbol.asyncIterator,r=Symbol.iterator);i--;){if(n&&null!=(t=e[n]))return t.call(e);if(r&&null!=(t=e[r]))return new o(t.call(e));n="@@asyncIterator",r="@@iterator";}throw new TypeError("Object is not async iterable")}function o(e){function t(e){if(Object(e)!==e)return Promise.reject(new TypeError(e+" is not an object."));var t=e.done;return Promise.resolve(e.value).then(function(e){return {value:e,done:t}})}return o=function(e){this.s=e,this.n=e.next;},o.prototype={s:null,n:null,next:function(){return t(this.n.apply(this.s,arguments))},return:function(e){var n=this.s.return;return void 0===n?Promise.resolve({value:e,done:!0}):t(n.apply(this.s,arguments))},throw:function(e){var n=this.s.return;return void 0===n?Promise.reject(e):t(n.apply(this.s,arguments))}},new o(e)}function i(e,t,n,r,o,i,a){try{var u=e[i](a),s=u.value;}catch(e){return void n(e)}u.done?t(s):Promise.resolve(s).then(r,o);}function a(e){return function(){var t=this,n=arguments;return new Promise(function(r,o){var a=e.apply(t,n);function u(e){i(a,r,o,u,s,"next",e);}function s(e){i(a,r,o,u,s,"throw",e);}u(void 0);})}}function u(t){return new e(t,0)}function s(e,t,n){return t=h(t),function(e,t){if(t&&("object"==typeof t||"function"==typeof t))return t;if(void 0!==t)throw new TypeError("Derived constructors may only return object or undefined");return function(e){if(void 0===e)throw new ReferenceError("this hasn't been initialised - super() hasn't been called");return e}(e)}(e,y()?Reflect.construct(t,n||[],h(e).constructor):t.apply(e,n))}function c(e,t){if(!(e instanceof t))throw new TypeError("Cannot call a class as a function")}function f(e,t){for(var n=0;n<t.length;n++){var r=t[n];r.enumerable=r.enumerable||!1,r.configurable=!0,"value"in r&&(r.writable=!0),Object.defineProperty(e,_(r.key),r);}}function l(e,t,n){return t&&f(e.prototype,t),n&&f(e,n),Object.defineProperty(e,"prototype",{writable:!1}),e}function d(e,t){var n="undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(!n){if(Array.isArray(e)||(n=A(e))||t){n&&(e=n);var r=0,o=function(){};return {s:o,n:function(){return r>=e.length?{done:!0}:{done:!1,value:e[r++]}},e:function(e){throw e},f:o}}throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}var i,a=!0,u=!1;return {s:function(){n=n.call(e);},n:function(){var e=n.next();return a=e.done,e},e:function(e){u=!0,i=e;},f:function(){try{a||null==n.return||n.return();}finally{if(u)throw i}}}}function p(e,t,n){return (t=_(t))in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function h(e){return h=Object.setPrototypeOf?Object.getPrototypeOf.bind():function(e){return e.__proto__||Object.getPrototypeOf(e)},h(e)}function v(e,t){if("function"!=typeof t&&null!==t)throw new TypeError("Super expression must either be null or a function");e.prototype=Object.create(t&&t.prototype,{constructor:{value:e,writable:!0,configurable:!0}}),Object.defineProperty(e,"prototype",{writable:!1}),t&&E(e,t);}function y(){try{var e=!Boolean.prototype.valueOf.call(Reflect.construct(Boolean,[],function(){}));}catch(e){}return (y=function(){return !!e})()}function b(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);t&&(r=r.filter(function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable})),n.push.apply(n,r);}return n}function m(e){for(var t=1;t<arguments.length;t++){var n=null!=arguments[t]?arguments[t]:{};t%2?b(Object(n),!0).forEach(function(t){p(e,t,n[t]);}):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(n)):b(Object(n)).forEach(function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(n,t));});}return e}function g(){
/*! regenerator-runtime -- Copyright (c) 2014-present, Facebook, Inc. -- license (MIT): https://github.com/babel/babel/blob/main/packages/babel-helpers/LICENSE */
var e,t,n="function"==typeof Symbol?Symbol:{},r=n.iterator||"@@iterator",o=n.toStringTag||"@@toStringTag";function i(n,r,o,i){var s=r&&r.prototype instanceof u?r:u,c=Object.create(s.prototype);return w(c,"_invoke",function(n,r,o){var i,u,s,c=0,f=o||[],l=!1,d={p:0,n:0,v:e,a:p,f:p.bind(e,4),d:function(t,n){return i=t,u=0,s=e,d.n=n,a}};function p(n,r){for(u=n,s=r,t=0;!l&&c&&!o&&t<f.length;t++){var o,i=f[t],p=d.p,h=i[2];n>3?(o=h===r)&&(s=i[(u=i[4])?5:(u=3,3)],i[4]=i[5]=e):i[0]<=p&&((o=n<2&&p<i[1])?(u=0,d.v=r,d.n=i[1]):p<h&&(o=n<3||i[0]>r||r>h)&&(i[4]=n,i[5]=r,d.n=h,u=0));}if(o||n>1)return a;throw l=!0,r}return function(o,f,h){if(c>1)throw TypeError("Generator is already running");for(l&&1===f&&p(f,h),u=f,s=h;(t=u<2?e:s)||!l;){i||(u?u<3?(u>1&&(d.n=-1),p(u,s)):d.n=s:d.v=s);try{if(c=2,i){if(u||(o="next"),t=i[o]){if(!(t=t.call(i,s)))throw TypeError("iterator result is not an object");if(!t.done)return t;s=t.value,u<2&&(u=0);}else 1===u&&(t=i.return)&&t.call(i),u<2&&(s=TypeError("The iterator does not provide a '"+o+"' method"),u=1);i=e;}else if((t=(l=d.n<0)?s:n.call(r,d))!==a)break}catch(t){i=e,u=1,s=t;}finally{c=1;}}return {value:t,done:l}}}(n,o,i),!0),c}var a={};function u(){}function s(){}function c(){}t=Object.getPrototypeOf;var f=[][r]?t(t([][r]())):(w(t={},r,function(){return this}),t),l=c.prototype=u.prototype=Object.create(f);function d(e){return Object.setPrototypeOf?Object.setPrototypeOf(e,c):(e.__proto__=c,w(e,o,"GeneratorFunction")),e.prototype=Object.create(l),e}return s.prototype=c,w(l,"constructor",c),w(c,"constructor",s),s.displayName="GeneratorFunction",w(c,o,"GeneratorFunction"),w(l),w(l,o,"Generator"),w(l,r,function(){return this}),w(l,"toString",function(){return "[object Generator]"}),(g=function(){return {w:i,m:d}})()}function w(e,t,n,r){var o=Object.defineProperty;try{o({},"",{});}catch(e){o=0;}w=function(e,t,n,r){function i(t,n){w(e,t,function(e){return this._invoke(t,n,e)});}t?o?o(e,t,{value:n,enumerable:!r,configurable:!r,writable:!r}):e[t]=n:(i("next",0),i("throw",1),i("return",2));},w(e,t,n,r);}function O(e){if(null!=e){var t=e["function"==typeof Symbol&&Symbol.iterator||"@@iterator"],n=0;if(t)return t.call(e);if("function"==typeof e.next)return e;if(!isNaN(e.length))return {next:function(){return e&&n>=e.length&&(e=void 0),{value:e&&e[n++],done:!e}}}}throw new TypeError(typeof e+" is not iterable")}function E(e,t){return E=Object.setPrototypeOf?Object.setPrototypeOf.bind():function(e,t){return e.__proto__=t,e},E(e,t)}function R(e,t){return function(e){if(Array.isArray(e))return e}(e)||function(e,t){var n=null==e?null:"undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(null!=n){var r,o,i,a,u=[],s=!0,c=!1;try{if(i=(n=n.call(e)).next,0===t){if(Object(n)!==n)return;s=!1;}else for(;!(s=(r=i.call(n)).done)&&(u.push(r.value),u.length!==t);s=!0);}catch(e){c=!0,o=e;}finally{try{if(!s&&null!=n.return&&(a=n.return(),Object(a)!==a))return}finally{if(c)throw o}}return u}}(e,t)||A(e,t)||function(){throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function S(e){return function(e){if(Array.isArray(e))return t(e)}(e)||function(e){if("undefined"!=typeof Symbol&&null!=e[Symbol.iterator]||null!=e["@@iterator"])return Array.from(e)}(e)||A(e)||function(){throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function _(e){var t=function(e,t){if("object"!=typeof e||!e)return e;var n=e[Symbol.toPrimitive];if(void 0!==n){var r=n.call(e,t);if("object"!=typeof r)return r;throw new TypeError("@@toPrimitive must return a primitive value.")}return ("string"===t?String:Number)(e)}(e,"string");return "symbol"==typeof t?t:t+""}function P(e){return P="function"==typeof Symbol&&"symbol"==typeof Symbol.iterator?function(e){return typeof e}:function(e){return e&&"function"==typeof Symbol&&e.constructor===Symbol&&e!==Symbol.prototype?"symbol":typeof e},P(e)}function A(e,n){if(e){if("string"==typeof e)return t(e,n);var r={}.toString.call(e).slice(8,-1);return "Object"===r&&e.constructor&&(r=e.constructor.name),"Map"===r||"Set"===r?Array.from(e):"Arguments"===r||/^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(r)?t(e,n):void 0}}function j(e){return function(){return new T(e.apply(this,arguments))}}function T(t){var n,r;function o(n,r){try{var a=t[n](r),u=a.value,s=u instanceof e;Promise.resolve(s?u.v:u).then(function(e){if(s){var r="return"===n&&u.k?n:"next";if(!u.k||e.done)return o(r,e);e=t[r](e).value;}i(!!a.done,e);},function(e){o("throw",e);});}catch(e){i(2,e);}}function i(e,t){2===e?n.reject(t):n.resolve({value:t,done:e}),(n=n.next)?o(n.key,n.arg):r=null;}this._invoke=function(e,t){return new Promise(function(i,a){var u={key:e,arg:t,resolve:i,reject:a,next:null};r?r=r.next=u:(n=r=u,o(e,t));})},"function"!=typeof t.return&&(this.return=void 0);}function k(e){var t="function"==typeof Map?new Map:void 0;return k=function(e){if(null===e||!function(e){try{return -1!==Function.toString.call(e).indexOf("[native code]")}catch(t){return "function"==typeof e}}(e))return e;if("function"!=typeof e)throw new TypeError("Super expression must either be null or a function");if(void 0!==t){if(t.has(e))return t.get(e);t.set(e,n);}function n(){return function(e,t,n){if(y())return Reflect.construct.apply(null,arguments);var r=[null];r.push.apply(r,t);var o=new(e.bind.apply(e,r));return n&&E(o,n.prototype),o}(e,arguments,h(this).constructor)}return n.prototype=Object.create(e.prototype,{constructor:{value:n,enumerable:!1,writable:!0,configurable:!0}}),E(n,e)},k(e)}function x(e,t){return function(){return e.apply(t,arguments)}}T.prototype["function"==typeof Symbol&&Symbol.asyncIterator||"@@asyncIterator"]=function(){return this},T.prototype.next=function(e){return this._invoke("next",e)},T.prototype.throw=function(e){return this._invoke("throw",e)},T.prototype.return=function(e){return this._invoke("return",e)};var C,N=Object.prototype.toString,D=Object.getPrototypeOf,U=Symbol.iterator,L=Symbol.toStringTag,F=function(){var e=Object.prototype.hasOwnProperty;return function(t,n){return e.call(t,n)}}(),B=function(e){return "string"==typeof e&&("__proto__"===e||"constructor"===e||"prototype"===e)},I=function(e,t,n){return e===Object.prototype||!n&&null===t},q=function(e,t){for(var n=e,r=[];null!=n;){if(-1!==r.indexOf(n))return !1;r.push(n);var o=D(n);if(I(n,o,n===e))return !1;if(F(n,t))return !0;n=o;}return !1},M=(C=Object.create(null),function(e){var t=N.call(e);return C[t]||(C[t]=t.slice(8,-1).toLowerCase())}),z=function(e){return e=e.toLowerCase(),function(t){return M(t)===e}},H=function(e){return function(t){return P(t)===e}},W=Array.isArray,J=H("undefined");function V(e){return null!==e&&!J(e)&&null!==e.constructor&&!J(e.constructor)&&G(e.constructor.isBuffer)&&e.constructor.isBuffer(e)}var K=z("ArrayBuffer");var X=H("string"),G=H("function"),$=H("number"),Q=function(e){return null!==e&&"object"===P(e)},Z=function(e){if(!Q(e))return !1;var t=D(e);return !(null!==t&&t!==Object.prototype&&null!==D(t)||q(e,L)||q(e,U))},Y=z("Date"),ee=z("File"),te=z("Blob"),ne=z("FileList"),re=z("Set");var oe="undefined"!=typeof globalThis?globalThis:"undefined"!=typeof self?self:"undefined"!=typeof window?window:"undefined"!=typeof global?global:{},ie=void 0!==oe.FormData?oe.FormData:void 0,ae=z("URLSearchParams"),ue=R(["ReadableStream","Request","Response","Headers"].map(z),4),se=ue[0],ce=ue[1],fe=ue[2],le=ue[3];function de(e,t){var n,r,o=(arguments.length>2&&void 0!==arguments[2]?arguments[2]:{}).allOwnKeys,i=void 0!==o&&o;if(null!=e)if("object"!==P(e)&&(e=[e]),W(e))for(n=0,r=e.length;n<r;n++)t.call(null,e[n],n,e);else {if(V(e))return;var a,u=i?Object.getOwnPropertyNames(e):Object.keys(e),s=u.length;for(n=0;n<s;n++)a=u[n],t.call(null,e[a],a,e);}}function pe(e,t){if(V(e))return null;t=t.toLowerCase();for(var n,r=Object.keys(e),o=r.length;o-- >0;)if(t===(n=r[o]).toLowerCase())return n;return null}var he="undefined"!=typeof globalThis?globalThis:"undefined"!=typeof self?self:"undefined"!=typeof window?window:global,ve=function(e){return !J(e)&&e!==he};var ye,be=(ye="undefined"!=typeof Uint8Array&&D(Uint8Array),function(e){return ye&&e instanceof ye}),me=z("HTMLFormElement"),ge=Object.prototype.propertyIsEnumerable,we=z("RegExp"),Oe=function(e,t){var n=Object.getOwnPropertyDescriptors(e),r={};de(n,function(n,o){var i;!1!==(i=t(n,o,e))&&(r[o]=i||n);}),Object.defineProperties(e,r);};var Ee,Re,Se,_e,Pe=z("AsyncFunction"),Ae=(Ee="function"==typeof setImmediate,Re=G(he.postMessage),Ee?setImmediate:Re?(Se="axios@".concat(Math.random()),_e=[],he.addEventListener("message",function(e){var t=e.source,n=e.data;t===he&&n===Se&&_e.length&&_e.shift()();},!1),function(e){_e.push(e),he.postMessage(Se,"*");}):function(e){return setTimeout(e)}),je="undefined"!=typeof queueMicrotask?queueMicrotask.bind(he):"undefined"!=typeof process&&process.nextTick||Ae,Te=function(e){return null!=e&&G(e[U])},ke={isArray:W,isArrayBuffer:K,isBuffer:V,isFormData:function(e){if(!e)return !1;if(ie&&e instanceof ie)return !0;var t=D(e);if(!t||t===Object.prototype)return !1;if(!G(e.append))return !1;var n=M(e);return "formdata"===n||"object"===n&&G(e.toString)&&"[object FormData]"===e.toString()},isArrayBufferView:function(e){return "undefined"!=typeof ArrayBuffer&&ArrayBuffer.isView?ArrayBuffer.isView(e):e&&e.buffer&&K(e.buffer)},isString:X,isNumber:$,isBoolean:function(e){return !0===e||!1===e},isObject:Q,isPlainObject:Z,isEmptyObject:function(e){if(!Q(e)||V(e))return !1;try{return 0===Object.keys(e).length&&Object.getPrototypeOf(e)===Object.prototype}catch(e){return !1}},isReadableStream:se,isRequest:ce,isResponse:fe,isHeaders:le,isUndefined:J,isDate:Y,isFile:ee,isReactNativeBlob:function(e){return !(!e||void 0===e.uri)},isReactNative:function(e){return e&&void 0!==e.getParts},isBlob:te,isRegExp:we,isFunction:G,isStream:function(e){return Q(e)&&G(e.pipe)},isURLSearchParams:ae,isTypedArray:be,isFileList:ne,forEach:de,merge:function e(){for(var t=ve(this)&&this||{},n=t.caseless,r=t.skipUndefined,o={},i=function(t,i){if("__proto__"!==i&&"constructor"!==i&&"prototype"!==i){var a=n&&"string"==typeof i&&pe(o,i)||i,u=F(o,a)?o[a]:void 0;Z(u)&&Z(t)?o[a]=e(u,t):Z(t)?o[a]=e({},t):W(t)?o[a]=t.slice():r&&J(t)||(o[a]=t);}},a=0,u=arguments.length;a<u;a++){var s=a<0||arguments.length<=a?void 0:arguments[a];if(s&&!V(s)&&(de(s,i),"object"===P(s)&&!W(s)))for(var c=Object.getOwnPropertySymbols(s),f=0;f<c.length;f++){var l=c[f];ge.call(s,l)&&i(s[l],l);}}return o},extend:function(e,t,n){return de(t,function(t,r){n&&G(t)?Object.defineProperty(e,r,{__proto__:null,value:x(t,n),writable:!0,enumerable:!0,configurable:!0}):Object.defineProperty(e,r,{__proto__:null,value:t,writable:!0,enumerable:!0,configurable:!0});},{allOwnKeys:(arguments.length>3&&void 0!==arguments[3]?arguments[3]:{}).allOwnKeys}),e},trim:function(e){return e.trim?e.trim():e.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,"")},stripBOM:function(e){return 65279===e.charCodeAt(0)&&(e=e.slice(1)),e},inherits:function(e,t,n,r){e.prototype=Object.create(t.prototype,r),Object.defineProperty(e.prototype,"constructor",{__proto__:null,value:e,writable:!0,enumerable:!1,configurable:!0}),Object.defineProperty(e,"super",{__proto__:null,value:t.prototype}),n&&Object.assign(e.prototype,n);},toFlatObject:function(e,t,n,r){var o,i,a,u={};if(t=t||{},null==e)return t;do{for(i=(o=Object.getOwnPropertyNames(e)).length;i-- >0;)a=o[i],r&&!r(a,e,t)||u[a]||(t[a]=e[a],u[a]=!0);e=!1!==n&&D(e);}while(e&&(!n||n(e,t))&&e!==Object.prototype);return t},kindOf:M,kindOfTest:z,endsWith:function(e,t,n){e=String(e),(void 0===n||n>e.length)&&(n=e.length),n-=t.length;var r=e.indexOf(t,n);return -1!==r&&r===n},toArray:function(e){if(!e)return null;if(W(e))return e;var t=e.length;if(!$(t))return null;for(var n=new Array(t);t-- >0;)n[t]=e[t];return n},forEachEntry:function(e,t){for(var n,r=(e&&e[U]).call(e);(n=r.next())&&!n.done;){var o=n.value;t.call(e,o[0],o[1]);}},matchAll:function(e,t){for(var n,r=[];null!==(n=e.exec(t));)r.push(n);return r},isHTMLForm:me,hasOwnProperty:F,hasOwnProp:F,hasOwnInPrototypeChain:q,getSafeProp:function(e,t){return null!=e&&q(e,t)?e[t]:void 0},toSafeFlatObject:function(e){if(null==e||"object"!==P(e)&&"function"!=typeof e)return e;var t=D(e);if(null===t&&function(e){if(!Object.isExtensible(e))return !1;var t=Object.getOwnPropertyNames(e);return Object.getOwnPropertySymbols&&t.push.apply(t,S(Object.getOwnPropertySymbols(e))),t.every(function(t){if(B(t))return !1;var n=Object.getOwnPropertyDescriptor(e,t);return !!n&&n.configurable&&!0===n.writable})}(e))return e;for(var n=Object.create(null),r=Object.create(null),o=[],i=e;null!=i&&-1===o.indexOf(i);){o.push(i);var a=i===e?t:D(i);if(I(i,a,i===e))break;var u=Object.getOwnPropertyNames(i);Object.getOwnPropertySymbols&&u.push.apply(u,S(Object.getOwnPropertySymbols(i)));var s,c=d(u);try{for(c.s();!(s=c.n()).done;){var f=s.value;B(f)||(F(r,f)||(n[f]=e[f],r[f]=!0));}}catch(e){c.e(e);}finally{c.f();}i=a;}return n},reduceDescriptors:Oe,freezeMethods:function(e){Oe(e,function(t,n){if(G(e)&&["arguments","caller","callee"].includes(n))return !1;var r=e[n];G(r)&&(t.enumerable=!1,"writable"in t?t.writable=!1:t.set||(t.set=function(){throw Error("Can not rewrite read-only method '"+n+"'")}));});},toObjectSet:function(e,t){var n={},r=function(e){e.forEach(function(e){n[e]=!0;});};return W(e)?r(e):r(String(e).split(t)),n},toCamelCase:function(e){return e.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g,function(e,t,n){return t.toUpperCase()+n})},noop:function(){},toFiniteNumber:function(e,t){return null!=e&&Number.isFinite(e=+e)?e:t},findKey:pe,global:he,isContextDefined:ve,isSpecCompliantForm:function(e){return !!(e&&G(e.append)&&"FormData"===e[L]&&e[U])},toJSONObject:function(e){var t=new WeakSet,n=function(e){if(Q(e)){if(t.has(e))return;if(V(e))return e;if(!("toJSON"in e)){var r;if(t.add(e),re(e)){r=[];var o,i=d(e);try{for(i.s();!(o=i.n()).done;){var a=o.value,u=n(a);!J(u)&&r.push(u);}}catch(e){i.e(e);}finally{i.f();}}else r=W(e)?[]:{},de(e,function(e,t){var o=n(e);!J(o)&&(r[t]=o);});return t.delete(e),r}}return e};return n(e)},isAsyncFn:Pe,isThenable:function(e){return e&&(Q(e)||G(e))&&G(e.then)&&G(e.catch)},setImmediate:Ae,asap:je,isIterable:Te,isSafeIterable:function(e){return null!=e&&q(e,U)&&Te(e)}},xe=ke.toObjectSet(["age","authorization","content-length","content-type","etag","expires","from","host","if-modified-since","if-unmodified-since","last-modified","location","max-forwards","proxy-authorization","referer","retry-after","user-agent"]);var Ce=new RegExp("[\\u0000-\\u0008\\u000a-\\u001f\\u007f]+","g"),Ne=new RegExp("[^\\u0009\\u0020-\\u007e\\u0080-\\u00ff]+","g");function De(e,t){return ke.isArray(e)?e.map(function(e){return De(e,t)}):function(e){for(var t=0,n=e.length;t<n;){var r=e.charCodeAt(t);if(9!==r&&32!==r)break;t+=1;}for(;n>t;){var o=e.charCodeAt(n-1);if(9!==o&&32!==o)break;n-=1;}return 0===t&&n===e.length?e:e.slice(t,n)}(String(e).replace(t,""))}function Ue(e){var t=Object.create(null);return ke.forEach(e.toJSON(),function(e,n){t[n]=function(e){return De(e,Ne)}(e);}),t}var Le=Symbol("internals");function Fe(e){return e&&String(e).trim().toLowerCase()}function Be(e){return !1===e||null==e?e:ke.isArray(e)?e.map(Be):function(e){return De(e,Ce)}(String(e))}var Ie=/^[!#$%&'*+\-.^_`|~0-9A-Za-z]+$/;function qe(e){for(var t=0,n=e.length;t<n;){var r=e.charCodeAt(t);if(9!==r&&32!==r)break;t+=1;}for(;n>t;){var o=e.charCodeAt(n-1);if(9!==o&&32!==o)break;n-=1;}return 0===t&&n===e.length?e:e.slice(t,n)}function Me(e,t,n,r,o){return ke.isFunction(r)?r.call(this,t,n):(o&&(t=n),ke.isString(t)?ke.isString(r)?-1!==t.indexOf(r):ke.isRegExp(r)?r.test(t):void 0:void 0)}var ze=function(){return l(function e(t){c(this,e),t&&this.set(t);},[{key:"set",value:function(e,t,n){var r=this;function o(e,t,n){var o=Fe(t);if(o){var i=ke.findKey(r,o);(!i||void 0===r[i]||!0===n||void 0===n&&!1!==r[i])&&(r[i||t]=Be(e));}}var i=function(e,t){return ke.forEach(e,function(e,n){return o(e,n,t)})};if(ke.isPlainObject(e)||e instanceof this.constructor)i(e,t);else if(ke.isString(e)&&(e=e.trim())&&!/^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(e.trim()))i(function(e){var t,n,r,o={};return e&&e.split("\n").forEach(function(e){r=e.indexOf(":"),t=e.substring(0,r).trim().toLowerCase(),n=e.substring(r+1).trim();var i=ke.hasOwnProp(o,t);!t||i&&ke.hasOwnProp(xe,t)||("set-cookie"===t?i?o[t].push(n):o[t]=[n]:o[t]=i?o[t]+", "+n:n);}),o}(e),t);else if(ke.isObject(e)&&ke.isSafeIterable(e)){var a,u,s,c=Object.create(null),f=d(e);try{for(f.s();!(s=f.n()).done;){var l=s.value;if(!ke.isArray(l))throw new TypeError("Object iterator must return a key-value pair");u=l[0],ke.hasOwnProp(c,u)?(a=c[u],c[u]=ke.isArray(a)?[].concat(S(a),[l[1]]):[a,l[1]]):c[u]=l[1];}}catch(e){f.e(e);}finally{f.f();}i(c,t);}else null!=e&&o(t,e,n);return this}},{key:"get",value:function(e,t){if(e=Fe(e)){var n=ke.findKey(this,e);if(n){var r=this[n];if(!t)return r;if(!0===t)return function(e){for(var t,n=Object.create(null),r=/([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;t=r.exec(e);)n[t[1]]=t[2];return n}(r);if(ke.isFunction(t))return t.call(this,r,n);if(ke.isRegExp(t))return t.exec(r);throw new TypeError("parser must be boolean|regexp|function")}}}},{key:"has",value:function(e,t){if(e=Fe(e)){var n=ke.findKey(this,e);return !(!n||void 0===this[n]||t&&!Me(0,this[n],n,t))}return !1}},{key:"delete",value:function(e,t){var n=this,r=!1;function o(e){if(e=Fe(e)){var o=ke.findKey(n,e);!o||t&&!Me(0,n[o],o,t)||(delete n[o],r=!0);}}return ke.isArray(e)?e.forEach(o):o(e),r}},{key:"clear",value:function(e){for(var t=Object.keys(this),n=t.length,r=!1;n--;){var o=t[n];e&&!Me(0,this[o],o,e,!0)||(delete this[o],r=!0);}return r}},{key:"normalize",value:function(e){var t=this,n={};return ke.forEach(this,function(r,o){var i=ke.findKey(n,o);if(i)return t[i]=Be(r),void delete t[o];var a=e?function(e){return e.trim().toLowerCase().replace(/([a-z\d])(\w*)/g,function(e,t,n){return t.toUpperCase()+n})}(o):String(o).trim();a!==o&&delete t[o],t[a]=Be(r),n[a]=!0;}),this}},{key:"concat",value:function(){for(var e,t=arguments.length,n=new Array(t),r=0;r<t;r++)n[r]=arguments[r];return (e=this.constructor).concat.apply(e,[this].concat(n))}},{key:"toJSON",value:function(e){var t=Object.create(null);return ke.forEach(this,function(n,r){null!=n&&!1!==n&&(t[r]=e&&ke.isArray(n)?n.join(", "):n);}),t}},{key:Symbol.iterator,value:function(){return Object.entries(this.toJSON())[Symbol.iterator]()}},{key:"toString",value:function(){return Object.entries(this.toJSON()).map(function(e){var t=R(e,2);return t[0]+": "+t[1]}).join("\n")}},{key:"getSetCookie",value:function(){var e=this.get("set-cookie");return ke.isArray(e)?e:null==e||!1===e?[]:[e]}},{key:Symbol.toStringTag,get:function(){return "AxiosHeaders"}}],[{key:"from",value:function(e){return e instanceof this?e:new this(e)}},{key:"parseParameters",value:function(e){return function(e){var t=Object.create(null),n=String(e),r=0,o=!1,i=!1;function a(e){var o=qe(n.slice(r,e)),i=o.indexOf("=");if(!(i<1)){var a=qe(o.slice(0,i));if(Ie.test(a)){var u=a.toLowerCase();if("__proto__"!==u&&"constructor"!==u&&"prototype"!==u){var s=qe(o.slice(i+1));t[u]=function(e){var t=e.length-1;if(t<1||34!==e.charCodeAt(0)||34!==e.charCodeAt(t))return e;for(var n="",r=1;r<t;r++){var o=e.charCodeAt(r);if(34===o)return e;if(92===o&&(r+=1)>=t)return e;n+=e[r];}return n}(s);}}}}for(var u=0;u<n.length;u++){var s=n.charCodeAt(u);o?i?i=!1:92===s?i=!0:34===s&&(o=!1):34===s?o=!0:44!==s&&59!==s||(a(u),r=u+1);}return a(n.length),t}(e)}},{key:"concat",value:function(e){for(var t=new this(e),n=arguments.length,r=new Array(n>1?n-1:0),o=1;o<n;o++)r[o-1]=arguments[o];return r.forEach(function(e){return t.set(e)}),t}},{key:"accessor",value:function(e){var t=(this[Le]=this[Le]={accessors:{}}).accessors,n=this.prototype;function r(e){var r=Fe(e);t[r]||(!function(e,t){var n=ke.toCamelCase(" "+t);["get","set","has"].forEach(function(r){Object.defineProperty(e,r+n,{__proto__:null,value:function(e,n,o){return this[r].call(this,t,e,n,o)},configurable:!0});});}(n,e),t[r]=!0);}return ke.isArray(e)?e.forEach(r):r(e),this}}])}();ze.accessor(["Content-Type","Content-Length","Accept","Accept-Encoding","User-Agent","Authorization"]),ke.reduceDescriptors(ze.prototype,function(e,t){var n=e.value,r=t[0].toUpperCase()+t.slice(1);return {get:function(){return n},set:function(e){this[r]=e;}}}),ke.freezeMethods(ze);var He="[REDACTED ****]";function We(e,t){var n=new Set(t.map(function(e){return String(e).toLowerCase()})),r=[],o=function(e){if(null===e||"object"!==P(e))return e;if(ke.isBuffer(e))return e;if(-1===r.indexOf(e)){var t;if(e instanceof ze&&(e=e.toJSON()),r.push(e),ke.isArray(e))t=[],e.forEach(function(e,n){var r=o(e);ke.isUndefined(r)||(t[n]=r);});else {if(!ke.isPlainObject(e)&&function(e){if(ke.hasOwnProp(e,"toJSON"))return !0;for(var t=Object.getPrototypeOf(e);t&&t!==Object.prototype;){if(ke.hasOwnProp(t,"toJSON"))return !0;t=Object.getPrototypeOf(t);}return !1}(e))return r.pop(),e;t=Object.create(null);for(var i=0,a=Object.entries(e);i<a.length;i++){var u=R(a[i],2),s=u[0],c=u[1],f=n.has(s.toLowerCase())?He:o(c);ke.isUndefined(f)||(t[s]=f);}}return r.pop(),t}};return o(e)}function Je(e){try{return String(e)}catch(e){return ""}}var Ve=function(e){function t(e,n,r,o,i){var a;return c(this,t),a=s(this,t,[e]),Object.defineProperty(a,"message",{__proto__:null,value:e,enumerable:!0,writable:!0,configurable:!0}),a.name="AxiosError",a.isAxiosError=!0,n&&(a.code=n),r&&(a.config=r),o&&(a.request=o),i&&(a.response=i,a.status=i.status),a}return v(t,e),l(t,[{key:"toJSON",value:function(){var e=this.config,t=e&&ke.hasOwnProp(e,"redact")?e.redact:void 0,n=ke.isArray(t)&&t.length>0?We(e,t):ke.toJSONObject(e);return {message:this.message,name:this.name,description:this.description,number:this.number,fileName:this.fileName,lineNumber:this.lineNumber,columnNumber:this.columnNumber,stack:this.stack,config:n,code:this.code,status:this.status}}}],[{key:"from",value:function(e,n,r,o,i,a){var u=e.message;!u&&ke.isArray(e.errors)&&e.errors.length&&(u=function(e){return e.errors.map(function(e){try{return e&&e.message?Je(e.message):Je(e)}catch(e){return ""}}).filter(Boolean).join("; ")||e.name||"AggregateError"}(e));var s=new t(u,n||e.code,r,o,i);return Object.defineProperty(s,"cause",{__proto__:null,value:e,writable:!0,enumerable:!1,configurable:!0}),s.name=e.name,null!=e.status&&null==s.status&&(s.status=e.status),a&&Object.assign(s,a),s}}])}(k(Error));Ve.ERR_BAD_OPTION_VALUE="ERR_BAD_OPTION_VALUE",Ve.ERR_BAD_OPTION="ERR_BAD_OPTION",Ve.ECONNABORTED="ECONNABORTED",Ve.ETIMEDOUT="ETIMEDOUT",Ve.ECONNREFUSED="ECONNREFUSED",Ve.ERR_NETWORK="ERR_NETWORK",Ve.ERR_FR_TOO_MANY_REDIRECTS="ERR_FR_TOO_MANY_REDIRECTS",Ve.ERR_DEPRECATED="ERR_DEPRECATED",Ve.ERR_BAD_RESPONSE="ERR_BAD_RESPONSE",Ve.ERR_BAD_REQUEST="ERR_BAD_REQUEST",Ve.ERR_CANCELED="ERR_CANCELED",Ve.ERR_NOT_SUPPORT="ERR_NOT_SUPPORT",Ve.ERR_INVALID_URL="ERR_INVALID_URL",Ve.ERR_FORM_DATA_DEPTH_EXCEEDED="ERR_FORM_DATA_DEPTH_EXCEEDED";function Ke(e){return ke.isPlainObject(e)||ke.isArray(e)}function Xe(e){return ke.endsWith(e,"[]")?e.slice(0,-2):e}function Ge(e,t,n){return e?e.concat(t).map(function(e,t){return e=Xe(e),!n&&t?"["+e+"]":e}).join(n?".":""):t}var $e=ke.toFlatObject(ke,{},null,function(e){return /^is[A-Z]/.test(e)});function Qe(e,t,n){if(!ke.isObject(e))throw new TypeError("target must be an object");t=t||new FormData;var r=function(e,t){var r=ke.getSafeProp(n,e);return ke.isUndefined(r)?t:r},o=r("metaTokens",!0),i=r("visitor")||h,a=r("dots",!1),u=r("indexes",!1),s=r("Blob")||"undefined"!=typeof Blob&&Blob,c=r("maxDepth",100),f=s&&ke.isSpecCompliantForm(t),l=[];if(!ke.isFunction(i))throw new TypeError("visitor must be a function");function d(e){if(null===e)return "";if(ke.isDate(e))return e.toISOString();if(ke.isBoolean(e))return e.toString();if(!f&&ke.isBlob(e))throw new Ve("Blob is not supported. Use a Buffer instead.");if(ke.isArrayBuffer(e)||ke.isTypedArray(e)){if(f&&"function"==typeof s)return new s([e]);throw new Ve("Blob is not supported. Use a Buffer instead.",Ve.ERR_NOT_SUPPORT)}return e}function p(e){if(e>c)throw new Ve("Object is too deeply nested ("+e+" levels). Max depth: "+c,Ve.ERR_FORM_DATA_DEPTH_EXCEEDED)}function h(e,n,r){var i=e;if(ke.isReactNative(t)&&ke.isReactNativeBlob(e))return t.append(Ge(r,n,a),d(e)),!1;if(e&&!r&&"object"===P(e))if(ke.endsWith(n,"{}"))n=o?n:n.slice(0,-2),e=function(e,t){if(c===1/0)return JSON.stringify(e);var n=[];return JSON.stringify(e,function(e,r){if(!ke.isObject(r))return r;for(;n.length&&n[n.length-1]!==this;)n.pop();return n.push(r),p(t+n.length-1),r})}(e,1);else if(ke.isArray(e)&&function(e){return ke.isArray(e)&&!e.some(Ke)}(e)||(ke.isFileList(e)||ke.endsWith(n,"[]"))&&(i=ke.toArray(e)))return n=Xe(n),i.forEach(function(e,r){!ke.isUndefined(e)&&null!==e&&t.append(!0===u?Ge([n],r,a):null===u?n:n+"[]",d(e));}),!1;return !!Ke(e)||(t.append(Ge(r,n,a),d(e)),!1)}var v=Object.assign($e,{defaultVisitor:h,convertValue:d,isVisitable:Ke});if(!ke.isObject(e))throw new TypeError("data must be an object");return function e(n,r){var o=arguments.length>2&&void 0!==arguments[2]?arguments[2]:0;if(!ke.isUndefined(n)){if(p(o),-1!==l.indexOf(n))throw new Error("Circular reference detected in "+r.join("."));l.push(n),ke.forEach(n,function(n,a){!0===(!(ke.isUndefined(n)||null===n)&&i.call(t,n,ke.isString(a)?a.trim():a,r,v))&&e(n,r?r.concat(a):[a],o+1);}),l.pop();}}(e),t}function Ze(e){var t={"!":"%21","'":"%27","(":"%28",")":"%29","~":"%7E","%20":"+"};return encodeURIComponent(e).replace(/[!'()~]|%20/g,function(e){return t[e]})}function Ye(e,t){this._pairs=[],e&&Qe(e,this,t);}var et=Ye.prototype;function tt(e){return encodeURIComponent(e).replace(/%3A/gi,":").replace(/%24/g,"$").replace(/%2C/gi,",").replace(/%20/g,"+")}function nt(e,t,n){if(!t)return e;e=e||"";var r,o=ke.isFunction(n)?{serialize:n}:n,i=ke.getSafeProp(o,"encode")||tt,a=ke.getSafeProp(o,"serialize");if(r=a?a(t,o):ke.isURLSearchParams(t)?t.toString():new Ye(t,o).toString(i)){var u=e.indexOf("#");-1!==u&&(e=e.slice(0,u)),e+=(-1===e.indexOf("?")?"?":"&")+r;}return e}et.append=function(e,t){this._pairs.push([e,t]);},et.toString=function(e){var t=this,n=e?function(n){return e.call(t,n,Ze)}:Ze;return this._pairs.map(function(e){return n(e[0])+"="+n(e[1])},"").join("&")};var rt=Symbol("internals");function ot(e){return e?e.length:0}function it(e){if(e)for(;e.length&&null===e[e.length-1];)e.pop();}function at(e,t){var n=e.handlers,r=ot(n);n!==t.handlersRef?(t.handlersRef=n,t.handlerEntries.clear()):r!==t.handlersLength&&(r?t.handlerEntries.forEach(function(e,r){n[e.index]!==e.handler&&t.handlerEntries.delete(r);}):t.handlerEntries.clear()),t.handlersLength=r;}var ut=function(){return l(function e(){c(this,e),this.handlers=[],this[rt]={handlersRef:this.handlers,handlersLength:this.handlers.length,handlerEntries:new Map,iterationDepth:0,nextId:0};},[{key:"use",value:function(e,t,n){var r={fulfilled:e,rejected:t,synchronous:!!n&&n.synchronous,runWhen:n?n.runWhen:null},o=this[rt];null==this.handlers&&(this.handlers=[]),at(this,o);var i=o.nextId++;return this.handlers.push(r),o.handlerEntries.set(i,{handler:r,index:this.handlers.length-1}),o.handlersLength=this.handlers.length,i}},{key:"eject",value:function(e){var t=this[rt];at(this,t);var n=t.handlerEntries.get(e);if(n){if(t.handlerEntries.delete(e),this.handlers[n.index]!==n.handler)return;this.handlers[n.index]=null,t.iterationDepth||(it(this.handlers),t.handlersLength=this.handlers.length);}}},{key:"clear",value:function(){this.handlers&&(this.handlers=[],at(this,this[rt]));}},{key:"forEach",value:function(e){var t=this[rt];at(this,t),t.iterationDepth++;try{ke.forEach(this.handlers,function(t){null!==t&&e(t);});}finally{--t.iterationDepth||(at(this,t),it(this.handlers),t.handlersLength=ot(this.handlers));}}}])}(),st={silentJSONParsing:!0,forcedJSONParsing:!0,clarifyTimeoutError:!1,legacyInterceptorReqResOrdering:!0,advertiseZstdAcceptEncoding:!1,validateStatusUndefinedResolves:!0},ct={isBrowser:!0,classes:{URLSearchParams:"undefined"!=typeof URLSearchParams?URLSearchParams:Ye,FormData:"undefined"!=typeof FormData?FormData:null,Blob:"undefined"!=typeof Blob?Blob:null},protocols:["http","https","file","blob","url","data"]},ft="undefined"!=typeof window&&"undefined"!=typeof document,lt="object"===("undefined"==typeof navigator?"undefined":P(navigator))&&navigator||void 0,dt=ft&&(!lt||["ReactNative","NativeScript","NS"].indexOf(lt.product)<0),pt="undefined"!=typeof WorkerGlobalScope&&self instanceof WorkerGlobalScope&&"function"==typeof self.importScripts,ht=ft&&window.location.href||"http://localhost",vt=m(m({},Object.freeze({__proto__:null,hasBrowserEnv:ft,hasStandardBrowserEnv:dt,hasStandardBrowserWebWorkerEnv:pt,navigator:lt,origin:ht})),ct);function yt(e){if(e>100)throw new Ve("FormData field is too deeply nested ("+e+" levels). Max depth: 100",Ve.ERR_FORM_DATA_DEPTH_EXCEEDED)}function bt(e){function t(e,n,r,o){yt(o);var i=e[o++];if("__proto__"===i)return !0;var a=Number.isFinite(+i),u=o>=e.length;return i=!i&&ke.isArray(r)?r.length:i,u?(ke.hasOwnProp(r,i)?r[i]=ke.isArray(r[i])?r[i].concat(n):[r[i],n]:r[i]=n,!a):(ke.hasOwnProp(r,i)&&ke.isObject(r[i])||(r[i]=[]),t(e,n,r[i],o)&&ke.isArray(r[i])&&(r[i]=function(e){var t,n,r={},o=Object.keys(e),i=o.length;for(t=0;t<i;t++)r[n=o[t]]=e[n];return r}(r[i])),!a)}if(ke.isFormData(e)&&ke.isFunction(e.entries)){var n={};return ke.forEachEntry(e,function(e,r){t(function(e){for(var t,n=[],r=/[^.[\]]+|\[([^.[\]]*)]/g;null!==(t=r.exec(e));)yt(n.length),n.push("[]"===t[0]?"":t[1]||t[0]);return n}(e),r,n,0);}),n}return null}var mt=Object.freeze(["get","delete","head","options","post","put","patch","purge","link","unlink","query"]),gt=function(e,t){return null!=e&&ke.hasOwnProp(e,t)?e[t]:void 0};var wt={transitional:st,adapter:["xhr","http","fetch"],transformRequest:[function(e,t){var n,r=t.getContentType()||"",o=r.indexOf("application/json")>-1,i=ke.isObject(e);if(i&&ke.isHTMLForm(e)&&(e=new FormData(e)),ke.isFormData(e))return o?JSON.stringify(bt(e)):e;if(ke.isArrayBuffer(e)||ke.isBuffer(e)||ke.isStream(e)||ke.isFile(e)||ke.isBlob(e)||ke.isReadableStream(e))return e;if(ke.isArrayBufferView(e))return e.buffer;if(ke.isURLSearchParams(e))return t.setContentType("application/x-www-form-urlencoded;charset=utf-8",!1),e.toString();if(i){var a=gt(this,"formSerializer");if(r.indexOf("application/x-www-form-urlencoded")>-1)return function(e,t){return Qe(e,new vt.classes.URLSearchParams,m({visitor:function(e,t,n,r){return vt.isNode&&ke.isBuffer(e)?(this.append(t,e.toString("base64")),!1):r.defaultVisitor.apply(this,arguments)}},t))}(e,a).toString();if((n=ke.isFileList(e))||r.indexOf("multipart/form-data")>-1){var u=gt(this,"env"),s=u&&u.FormData;return Qe(n?{"files[]":e}:e,s&&new s,a)}}return i||o?(t.setContentType("application/json",!1),function(e,t,n){if(ke.isString(e))try{return (t||JSON.parse)(e),ke.trim(e)}catch(e){if("SyntaxError"!==e.name)throw e}return (n||JSON.stringify)(e)}(e)):e}],transformResponse:[function(e){var t=gt(this,"transitional")||wt.transitional,n=t&&t.forcedJSONParsing,r=gt(this,"responseType"),o="json"===r;if(ke.isResponse(e)||ke.isReadableStream(e))return e;if(e&&ke.isString(e)&&(n&&!r||o)){var i=!(t&&t.silentJSONParsing)&&o;try{return JSON.parse(e,gt(this,"parseReviver"))}catch(e){if(i){if("SyntaxError"===e.name)throw Ve.from(e,Ve.ERR_BAD_RESPONSE,this,null,gt(this,"response"));throw e}}}return e}],timeout:0,xsrfCookieName:"XSRF-TOKEN",xsrfHeaderName:"X-XSRF-TOKEN",maxContentLength:-1,maxBodyLength:-1,env:{FormData:vt.classes.FormData,Blob:vt.classes.Blob},validateStatus:function(e){return e>=200&&e<300},headers:{common:{Accept:"application/json, text/plain, */*","Content-Type":void 0}}};function Ot(e,t){var n=this||wt,r=t||n,o=ze.from(r.headers),i=r.data;return ke.forEach(e,function(e){i=e.call(n,i,o.normalize(),t?t.status:void 0);}),o.normalize(),i}function Et(e){return !(!e||!e.__CANCEL__)}ke.forEach(mt,function(e){wt.headers[e]={};});var Rt=function(e){function t(e,n,r){var o;return c(this,t),(o=s(this,t,[null==e?"canceled":e,Ve.ERR_CANCELED,n,r])).name="CanceledError",o.__CANCEL__=!0,o}return v(t,e),l(t)}(Ve);function St(e,t,n){var r=n.config.validateStatus;n.status&&r&&!r(n.status)?t(new Ve("Request failed with status code "+n.status,n.status>=400&&n.status<500?Ve.ERR_BAD_REQUEST:Ve.ERR_BAD_RESPONSE,n.config,n.request,n)):e(n);}var _t=/[\t\n\r]/g;function Pt(e){if("string"!=typeof e)return e;for(var t=0;t<e.length&&e.charCodeAt(t)<=32;)t++;return e.slice(t).replace(_t,"")}function At(e){var t=/^([-+\w]{1,25}):(?:\/\/)?/.exec(e);return t&&t[1]||""}var jt=function(e,t){var n=arguments.length>2&&void 0!==arguments[2]?arguments[2]:3,r=0,o=function(e,t){e=e||10;var n,r=new Array(e),o=new Array(e),i=0,a=0;return t=void 0!==t?t:1e3,function(u){var s=Date.now(),c=o[a];n||(n=s),r[i]=u,o[i]=s;for(var f=a,l=0;f!==i;)l+=r[f++],f%=e;if((i=(i+1)%e)===a&&(a=(a+1)%e),!(s-n<t)){var d=c&&s-c;return d?Math.round(1e3*l/d):void 0}}}(50,250);return function(e,t){var n,r,o=0,i=1e3/t,a=function(t){var i=arguments.length>1&&void 0!==arguments[1]?arguments[1]:Date.now();o=i,n=null,r&&(clearTimeout(r),r=null),e.apply(void 0,S(t));};return [function(){for(var e=Date.now(),t=e-o,u=arguments.length,s=new Array(u),c=0;c<u;c++)s[c]=arguments[c];t>=i?a(s,e):(n=s,r||(r=setTimeout(function(){r=null,a(n);},i-t)));},function(){return n&&a(n)},function(){for(var e=arguments.length,t=new Array(e),n=0;n<e;n++)t[n]=arguments[n];return a(t)}]}(function(n){if(n&&ke.isNumber(n.loaded)){var i=n.loaded,a=n.lengthComputable?n.total:void 0,u=Math.max(0,null!=a?Math.min(i,a):i),s=Math.max(0,u-r),c=o(s);r=Math.max(r,u);var f=p({loaded:u,total:a,progress:a?u/a:void 0,bytes:s,rate:c||void 0,estimated:c&&a?(a-u)/c:void 0,event:n,lengthComputable:null!=a},t?"download":"upload",!0);e(f);}},n)},Tt=function(e,t){var n=null!=e;return [function(r){return t[0]({lengthComputable:n,total:e,loaded:r})},t[1]]},kt=function(e){var t=arguments.length>1&&void 0!==arguments[1]?arguments[1]:ke.asap;return function(){for(var n=arguments.length,r=new Array(n),o=0;o<n;o++)r[o]=arguments[o];return t(function(){return e.apply(void 0,r)})}},xt=vt.hasStandardBrowserEnv?function(e,t){return function(n){return n=new URL(n,vt.origin),e.protocol===n.protocol&&e.host===n.host&&(t||e.port===n.port)}}(new URL(vt.origin),vt.navigator&&/(msie|trident)/i.test(vt.navigator.userAgent)):function(){return !0},Ct=vt.hasStandardBrowserEnv?{write:function(e,t,n,r,o,i,a){if("undefined"!=typeof document){var u=["".concat(e,"=").concat(encodeURIComponent(t))];ke.isNumber(n)&&u.push("expires=".concat(new Date(n).toUTCString())),ke.isString(r)&&u.push("path=".concat(r)),ke.isString(o)&&u.push("domain=".concat(o)),!0===i&&u.push("secure"),ke.isString(a)&&u.push("SameSite=".concat(a)),document.cookie=u.join("; ");}},read:function(e){if("undefined"==typeof document)return null;for(var t=document.cookie.split(";"),n=0;n<t.length;n++){var r=t[n].replace(/^\s+/,""),o=r.indexOf("=");if(-1!==o&&r.slice(0,o)===e)try{return decodeURIComponent(r.slice(o+1))}catch(e){return r.slice(o+1)}}return null},remove:function(e){this.write(e,"",Date.now()-864e5,"/");}}:{write:function(){},read:function(){return null},remove:function(){}};var Nt=/^https?:(?!\/\/)/i;function Dt(e){var t,n=e.replace(/^(https?:\/{0,2})[^/?#]*@/i,"$1".concat(He,"@")),r=n.indexOf("#"),o=(-1===r?n:n.slice(0,r)).replace(/([?&][^=&#]*=)[^&#]*/g,"$1".concat(He));return -1===r?o:"".concat(o,"#").concat((t=n.slice(r+1))?t.replace(/(^|&)([^=&]*=)?[^&]+/g,function(e,t){var n=arguments.length>2&&void 0!==arguments[2]?arguments[2]:"";return "".concat(t).concat(n).concat(He)}):t)}function Ut(e,t){if("string"==typeof e){var n=Pt(e);if(Nt.test(n))throw new Ve("Invalid URL ".concat(JSON.stringify(Dt(n)),': missing "//" after protocol'),Ve.ERR_INVALID_URL,t)}}function Lt(e,t,n,r){Ut(t,r);var o,i=!("string"==typeof(o=t)&&/^([a-z][a-z\d+\-.]*:)?\/\//i.test(o));return e&&(i||!1===n)?(Ut(e,r),function(e,t){if(!t)return e;for(var n=e.length;n>0&&47===e.charCodeAt(n-1);)n--;return e.slice(0,n)+"/"+t.replace(/^\/+/,"")}(e,t)):t}var Ft=function(e){return e instanceof ze?m({},e):e};function Bt(e,t){e=e||{},t=t||{};var n=Object.create(null);function r(e,t,n,r){return ke.isPlainObject(e)&&ke.isPlainObject(t)?ke.merge.call({caseless:r},e,t):ke.isPlainObject(t)?ke.merge({},t):ke.isArray(t)?t.slice():t}function o(e,t,n,o){return ke.isUndefined(t)?ke.isUndefined(e)?void 0:r(void 0,e,0,o):r(e,t,0,o)}function i(e,t){if(!ke.isUndefined(t))return r(void 0,t)}function a(e,t){return ke.isUndefined(t)?ke.isUndefined(e)?void 0:r(void 0,e):r(void 0,t)}function u(n,o,i){return ke.hasOwnProp(t,i)?r(n,o):ke.hasOwnProp(e,i)?r(void 0,n):void 0}Object.defineProperty(n,"hasOwnProperty",{__proto__:null,value:Object.prototype.hasOwnProperty,enumerable:!1,writable:!0,configurable:!0});var s,c={url:i,method:i,data:i,baseURL:a,transformRequest:a,transformResponse:a,paramsSerializer:a,timeout:a,timeoutErrorMessage:a,withCredentials:a,withXSRFToken:a,adapter:a,responseType:a,xsrfCookieName:a,xsrfHeaderName:a,onUploadProgress:a,onDownloadProgress:a,decompress:a,maxContentLength:a,maxBodyLength:a,beforeRedirect:a,transport:a,httpAgent:a,httpsAgent:a,cancelToken:a,socketPath:a,allowedSocketPaths:a,responseEncoding:a,validateStatus:u,headers:function(e,t,n){return o(Ft(e),Ft(t),0,!0)}};return ke.forEach((s=m(m({},e),t),Object.getOwnPropertySymbols&&Object.getOwnPropertyDescriptor?Object.keys(s).concat(Object.getOwnPropertySymbols(s).filter(function(e){return Object.getOwnPropertyDescriptor(s,e).enumerable})):Object.keys(s)),function(r){if("__proto__"!==r&&"constructor"!==r&&"prototype"!==r){var i=ke.hasOwnProp(c,r)?c[r]:o,a=i(ke.hasOwnProp(e,r)?e[r]:void 0,ke.hasOwnProp(t,r)?t[r]:void 0,r);ke.isUndefined(a)&&i!==u||(n[r]=a);}}),ke.hasOwnProp(t,"validateStatus")&&ke.isUndefined(t.validateStatus)&&!1===function(n){var r=ke.hasOwnProp(t,"transitional")?t.transitional:void 0;if(!ke.isUndefined(r)){if(!ke.isPlainObject(r))return;if(ke.hasOwnProp(r,n))return r[n]}var o=ke.hasOwnProp(e,"transitional")?e.transitional:void 0;if(ke.isPlainObject(o)&&ke.hasOwnProp(o,n))return o[n]}("validateStatusUndefinedResolves")&&(ke.hasOwnProp(e,"validateStatus")?n.validateStatus=r(void 0,e.validateStatus):delete n.validateStatus),n}var It=["content-type","content-length"];function qt(e){var t=Bt({},e),n=function(e){return ke.hasOwnProp(t,e)?t[e]:void 0},r=n("data"),o=n("withXSRFToken"),i=n("xsrfHeaderName"),a=n("xsrfCookieName"),u=n("headers"),s=n("auth"),c=n("baseURL"),f=n("allowAbsoluteUrls"),l=n("url");if(t.headers=u=ze.from(u),t.url=nt(Lt(c,l,f,t),n("params"),n("paramsSerializer")),s){var d=ke.getSafeProp(s,"username")||"",p=ke.getSafeProp(s,"password")||"";try{u.set("Authorization","Basic "+btoa(d+":"+(p?encodeURIComponent(p).replace(/%([0-9A-F]{2})/gi,function(e,t){return String.fromCharCode(parseInt(t,16))}):"")));}catch(t){throw Ve.from(t,Ve.ERR_BAD_OPTION_VALUE,e)}}if(ke.isFormData(r)){var h=ke.getSafeProp(r,"getHeaders");vt.hasStandardBrowserEnv||vt.hasStandardBrowserWebWorkerEnv||ke.isReactNative(r)?u.setContentType(void 0):ke.isFunction(h)&&function(e,t,n){"content-only"===n?Object.entries(t||{}).forEach(function(t){var n=R(t,2),r=n[0],o=n[1];It.includes(r.toLowerCase())&&e.set(r,o);}):e.set(t);}(u,h.call(r),n("formDataHeaderPolicy"));}if(vt.hasStandardBrowserEnv&&(ke.isFunction(o)&&(o=o(t)),!0===o||null==o&&xt(t.url))){var v=i&&a&&Ct.read(a);v&&u.set(i,v);}return t}var Mt="undefined"!=typeof XMLHttpRequest&&function(e){return new Promise(function(t,n){var r,o,i,a,u,s,c=qt(e),f=c.data,l=ze.from(c.headers).normalize(),d=c.responseType,p=c.onUploadProgress,h=c.onDownloadProgress;function v(){a&&a(),u&&u(),c.cancelToken&&c.cancelToken.unsubscribe(r),c.signal&&c.signal.removeEventListener("abort",r);}var y=new XMLHttpRequest;function b(r){if(y){if(!(0!==y.status||"file"===(At(Pt(c.url))||At(vt.origin))||y.responseURL&&y.responseURL.startsWith("file:")))return n(new Ve("Request aborted",Ve.ECONNABORTED,e,y)),v(),void(y=null);try{r?s&&s(r):u&&u();}catch(e){setTimeout(function(){throw e});}if(y){var o=ze.from("getAllResponseHeaders"in y&&y.getAllResponseHeaders());St(function(e){t(e),v();},function(e){n(e),v();},{data:d&&"text"!==d&&"json"!==d?y.response:y.responseText,status:y.status,statusText:y.statusText,headers:o,config:e,request:y}),y=null;}}}if(y.open(c.method.toUpperCase(),c.url,!0),y.timeout=c.timeout,"onloadend"in y?y.onloadend=b:y.onreadystatechange=function(){y&&4===y.readyState&&(0!==y.status||y.responseURL&&y.responseURL.startsWith("file:"))&&setTimeout(b);},y.onabort=function(){y&&(n(new Ve("Request aborted",Ve.ECONNABORTED,e,y)),v(),y=null);},y.onerror=function(t){var r=t&&t.message?t.message:"Network Error",o=new Ve(r,Ve.ERR_NETWORK,e,y);o.event=t||null,n(o),v(),y=null;},y.ontimeout=function(){var t=c.timeout?"timeout of "+c.timeout+"ms exceeded":"timeout exceeded",r=c.transitional||st;c.timeoutErrorMessage&&(t=c.timeoutErrorMessage),n(new Ve(t,r.clarifyTimeoutError?Ve.ETIMEDOUT:Ve.ECONNABORTED,e,y)),v(),y=null;},void 0===f&&l.setContentType(null),"setRequestHeader"in y&&ke.forEach(Ue(l),function(e,t){y.setRequestHeader(t,e);}),ke.isUndefined(c.withCredentials)||(y.withCredentials=!!c.withCredentials),d&&"json"!==d&&(y.responseType=c.responseType),h){var m=R(jt(h,!0),3);i=m[0],u=m[1],s=m[2],y.addEventListener("progress",i);}if(p&&y.upload){var g=R(jt(p),2);o=g[0],a=g[1],y.upload.addEventListener("progress",o),y.upload.addEventListener("loadend",a);}(c.cancelToken||c.signal)&&(r=function(t){y&&(n(!t||t.type?new Rt(null,e,y):t),y.abort(),v(),y=null);},c.cancelToken&&c.cancelToken.subscribe(r),c.signal&&(c.signal.aborted?r():c.signal.addEventListener("abort",r)));var w=At(c.url);if(w&&!vt.protocols.includes(w))return n(new Ve("Unsupported protocol "+w+":",Ve.ERR_BAD_REQUEST,e)),void v();y.send(f||null);})},zt=function(e,t){if(e=e?e.filter(Boolean):[],t||e.length){var n=new AbortController,r=!1,o=function(e){if(!r){r=!0,a();var t=e instanceof Error?e:this.reason;n.abort(t instanceof Ve?t:new Rt(t instanceof Error?t.message:t));}},i=t&&setTimeout(function(){i=null,o(new Ve("timeout of ".concat(t,"ms exceeded"),Ve.ETIMEDOUT));},t),a=function(){e&&(i&&clearTimeout(i),i=null,e.forEach(function(e){e.unsubscribe?e.unsubscribe(o):e.removeEventListener("abort",o);}),e=null);};e.forEach(function(e){r||(e.aborted?o.call(e):e.addEventListener("abort",o,{once:!0}));});var u=n.signal;return u.unsubscribe=function(){return ke.asap(a)},u}},Ht=g().m(function e(t,n){var r,o,i;return g().w(function(e){for(;;)switch(e.n){case 0:if(r=t.byteLength,n&&!(r<n)){e.n=2;break}return e.n=1,t;case 1:return e.a(2);case 2:o=0;case 3:if(!(o<r)){e.n=5;break}return i=o+n,e.n=4,t.slice(o,i);case 4:o=i,e.n=3;break;case 5:return e.a(2)}},e)}),Wt=function(){var e=j(g().m(function e(t,o){var i,a,s,c,f,l,d;return g().w(function(e){for(;;)switch(e.p=e.n){case 0:i=!1,a=!1,e.p=1,c=r(Jt(t));case 2:return e.n=3,u(c.next());case 3:if(!(i=!(f=e.v).done)){e.n=5;break}return l=f.value,e.d(O(n(r(Ht(l,o)))),4);case 4:i=!1,e.n=2;break;case 5:e.n=7;break;case 6:e.p=6,d=e.v,a=!0,s=d;case 7:if(e.p=7,e.p=8,!i||null==c.return){e.n=9;break}return e.n=9,u(c.return());case 9:if(e.p=9,!a){e.n=10;break}throw s;case 10:return e.f(9);case 11:return e.f(7);case 12:return e.a(2)}},e,null,[[8,,9,11],[1,6,7,12]])}));return function(t,n){return e.apply(this,arguments)}}(),Jt=function(){var e=j(g().m(function e(t){var o,i,a,s;return g().w(function(e){for(;;)switch(e.p=e.n){case 0:if(!t[Symbol.asyncIterator]){e.n=2;break}return e.d(O(n(r(t))),1);case 1:return e.a(2);case 2:o=t.getReader(),e.p=3;case 4:return e.n=5,u(o.read());case 5:if(i=e.v,a=i.done,s=i.value,!a){e.n=6;break}return e.a(3,8);case 6:return e.n=7,s;case 7:e.n=4;break;case 8:return e.p=8,e.n=9,u(o.cancel());case 9:return e.f(8);case 10:return e.a(2)}},e,null,[[3,,8,10]])}));return function(t){return e.apply(this,arguments)}}(),Vt=function(e,t,n,r){var o,i=Wt(e,t),u=0,s=function(e){o||(o=!0,r&&r(e));};return new ReadableStream({pull:function(e){return a(g().m(function t(){var r,o,a,c,f,l;return g().w(function(t){for(;;)switch(t.p=t.n){case 0:return t.p=0,t.n=1,i.next();case 1:if(r=t.v,o=r.done,a=r.value,!o){t.n=2;break}return s(),e.close(),t.a(2);case 2:c=a.byteLength,n&&(f=u+=c,n(f)),e.enqueue(new Uint8Array(a)),t.n=4;break;case 3:throw t.p=3,l=t.v,s(l),l;case 4:return t.a(2)}},t,null,[[0,3]])}))()},cancel:function(e){return s(e),i.return()}},{highWaterMark:2})},Kt=function(e){return e>=48&&e<=57||e>=65&&e<=70||e>=97&&e<=102},Xt=function(e,t,n){return t+2<n&&Kt(e.charCodeAt(t+1))&&Kt(e.charCodeAt(t+2))},Gt=function(e){return e<=57?e-48:(223&e)-55},$t=function(e){return e>=65&&e<=90||e>=97&&e<=122||e>=48&&e<=57||43===e||47===e||45===e||95===e},Qt=function(e){return 9===e||10===e||12===e||13===e||32===e},Zt=function(e){for(var t=e.length,n=0,r=0,o=!1,i=0;i<t;i++){var a=e.charCodeAt(i);37===a&&Xt(e,i,t)&&(a=16*Gt(e.charCodeAt(i+1))+Gt(e.charCodeAt(i+2)),i+=2),Qt(a)||(61!==a?!$t(a)||r>0?o=!0:n++:r++);}return o||r>2||r>0&&(n+r)%4!=0||n%4==1?function(e){var t=e.length,n=0;return t>0&&61===e.charCodeAt(t-1)&&(n++,t>1&&61===e.charCodeAt(t-2)&&n++),Math.floor(3*(t-n)/4)}(e):function(e){var t=e%4;return 3*Math.floor(e/4)+(2===t?1:3===t?2:0)}(n)};function Yt(e){var t="string"==typeof e?e.indexOf("#"):-1;return function(e,t){if(!e||"string"!=typeof e)return 0;if(!e.startsWith("data:"))return 0;var n=e.indexOf(",");if(n<0)return 0;var r=e.slice(5,n),o=e.slice(n+1);if(/;base64/i.test(r))return t(o);for(var i=0,a=0,u=o.length;a<u;a++){var s=o.charCodeAt(a);if(37===s&&Xt(o,a,u))i+=1,a+=2;else if(s<128)i+=1;else if(s<2048)i+=2;else if(s>=55296&&s<=56319&&a+1<u){var c=o.charCodeAt(a+1);c>=56320&&c<=57343?(i+=4,a++):i+=3;}else i+=3;}return i}(-1===t?e:e.slice(0,t),Zt)}var en="1.20.0",tn={cache:"default",redirect:"follow",referrer:"about:client",referrerPolicy:"",mode:"cors",integrity:"",keepalive:!1,priority:"auto",window:null},nn=ke.isFunction,rn=function(e){return encodeURIComponent(e).replace(/%([0-9A-F]{2})/gi,function(e,t){return String.fromCharCode(parseInt(t,16))})},on=function(e){if(!ke.isString(e))return e;try{return decodeURIComponent(e)}catch(t){return e}},an=function(e){try{for(var t=arguments.length,n=new Array(t>1?t-1:0),r=1;r<t;r++)n[r-1]=arguments[r];return !!e.apply(void 0,n)}catch(e){return !1}},un=function(e){var t=e.indexOf("://"),n=e;return -1!==t&&(n=n.slice(t+3)),n.includes("@")||n.includes(":")},sn=function(e){var t=void 0!==ke.global&&null!==ke.global?ke.global:globalThis,n=t.ReadableStream,r=t.TextEncoder,o=e=ke.merge.call({skipUndefined:!0},{Request:t.Request,Response:t.Response},e),i=o.fetch,u=o.Request,s=o.Response,c=i?nn(i):"function"==typeof fetch,f=nn(u),l=nn(s);if(!c)return !1;var d,p=c&&nn(n),h=c&&("function"==typeof r?(d=new r,function(e){return d.encode(e)}):function(){var e=a(g().m(function e(t){var n,r;return g().w(function(e){for(;;)switch(e.n){case 0:return n=Uint8Array,e.n=1,new u(t).arrayBuffer();case 1:return r=e.v,e.a(2,new n(r))}},e)}));return function(t){return e.apply(this,arguments)}}()),v=f&&p&&an(function(){var e=!1,t=new u(vt.origin,{body:new n,method:"POST",get duplex(){return e=!0,"half"}}),r=t.headers.has("Content-Type");return null!=t.body&&t.body.cancel(),e&&!r}),y=l&&p&&an(function(){return ke.isReadableStream(new s("").body)}),b={stream:y&&function(e){return e.body}};c&&["text","arrayBuffer","blob","formData","stream"].forEach(function(e){!b[e]&&(b[e]=function(t,n){var r=t&&t[e];if(r)return r.call(t);throw new Ve("Response type '".concat(e,"' is not supported"),Ve.ERR_NOT_SUPPORT,n)});});var m=function(){var e=a(g().m(function e(t){var n;return g().w(function(e){for(;;)switch(e.n){case 0:if(null!=t){e.n=1;break}return e.a(2,0);case 1:if(!ke.isBlob(t)){e.n=2;break}return e.a(2,t.size);case 2:if(!ke.isSpecCompliantForm(t)){e.n=4;break}return n=new u(vt.origin,{method:"POST",body:t}),e.n=3,n.arrayBuffer();case 3:case 6:return e.a(2,e.v.byteLength);case 4:if(!ke.isArrayBufferView(t)&&!ke.isArrayBuffer(t)){e.n=5;break}return e.a(2,t.byteLength);case 5:if(ke.isURLSearchParams(t)&&(t+=""),!ke.isString(t)){e.n=7;break}return e.n=6,h(t);case 7:return e.a(2)}},e)}));return function(t){return e.apply(this,arguments)}}(),w=function(){var e=a(g().m(function e(t,n){var r;return g().w(function(e){for(;;)if(0===e.n)return r=ke.toFiniteNumber(t.getContentLength()),e.a(2,null==r?m(n):r)},e)}));return function(t,n){return e.apply(this,arguments)}}();return function(){var e=a(g().m(function e(t){var n,o,a,c,l,d,h,O,E,S,_,P,A,j,T,k,x,C,N,D,U,L,F,B,I,q,M,z,H,W,J,V,K,X,G,$,Q,Z,Y,ee,te,ne,re,oe,ie,ae,ue,se,ce,fe,le,de,pe,he,ve,ye,be,me,ge,we,Oe,Ee,Re,Se;return g().w(function(e){for(;;)switch(e.p=e.n){case 0:if(n=qt(t),o=n.url,a=n.method,c=n.data,l=n.signal,d=n.cancelToken,h=n.timeout,O=n.onDownloadProgress,E=n.onUploadProgress,S=n.responseType,_=n.headers,P=n.withCredentials,A=void 0===P?"same-origin":P,j=n.fetchOptions,T=n.maxContentLength,k=n.maxBodyLength,x=n.maxRedirects,C=ke.isNumber(T)&&T>-1,N=ke.isNumber(k)&&k>-1,D=function(e){return ke.hasOwnProp(t,e)?t[e]:void 0},U=i||fetch,S=S?(S+"").toLowerCase():"text",L=zt([l,d&&d.toAbortSignal()],h),F=null,B=L&&L.unsubscribe&&function(){L.unsubscribe();},q=null,M=function(){return new Ve("Request body larger than maxBodyLength limit",Ve.ERR_BAD_REQUEST,t,F)},e.p=1,z=void 0,(H=D("auth"))&&(W=ke.getSafeProp(H,"username")||"",J=ke.getSafeProp(H,"password")||"",z={username:W,password:J}),un(o)&&(V=new URL(o,vt.origin),z||!V.username&&!V.password||(K=on(V.username),X=on(V.password),z={username:K,password:X}),(V.username||V.password)&&(V.username="",V.password="",o=V.href)),z&&(_.delete("authorization"),_.set("Authorization","Basic "+btoa(rn((z.username||"")+":"+(z.password||""))))),!C||"string"!=typeof o||!o.startsWith("data:")){e.n=2;break}if(!(Yt(o)>T)){e.n=2;break}throw new Ve("maxContentLength size of "+T+" exceeded",Ve.ERR_BAD_RESPONSE,t,F);case 2:if(!N||"get"===a||"head"===a){e.n=4;break}return e.n=3,m(c);case 3:if("number"!=typeof(G=e.v)||!isFinite(G)){e.n=4;break}if(I=G,!(G>k)){e.n=4;break}throw M();case 4:if($=N&&(ke.isReadableStream(c)||ke.isStream(c)),Q=function(e,t,n){return Vt(e,65536,function(e){if(N&&e>k)throw q=M();t&&t(e);},n)},!v||"get"===a||"head"===a||!E&&!$){e.n=8;break}if(null!=I){e.n=6;break}return e.n=5,w(_,c);case 5:Re=e.v,e.n=7;break;case 6:Re=I;case 7:(0!==(I=Re)||$)&&(Z=new u(o,{method:"POST",body:c,duplex:"half"}),ke.isFormData(c)&&(Y=Z.headers.get("content-type"))&&_.setContentType(Y),Z.body&&(ee=E&&Tt(I,jt(kt(E)))||[],te=R(ee,2),ne=te[0],re=te[1],c=Q(Z.body,ne,re))),e.n=10;break;case 8:if(!$||f||!p||"get"===a||"head"===a){e.n=9;break}c=Q(c),e.n=10;break;case 9:if(!$||!f||v||"get"===a||"head"===a){e.n=10;break}throw new Ve("Stream request bodies are not supported by the current fetch implementation",Ve.ERR_NOT_SUPPORT,t,F);case 10:return ke.isString(A)||(A=A?"include":"omit"),oe=f&&"credentials"in u.prototype,ke.isFormData(c)&&(ie=_.getContentType())&&/^multipart\/form-data/i.test(ie)&&!/boundary=/i.test(ie)&&_.delete("content-type"),_.set("User-Agent","axios/"+en,!1),(ae=null==j?j:Object.assign(Object.create(null),j))&&(delete ae.body,delete ae.headers,delete ae.method,delete ae.signal,delete ae.duplex,delete ae.credentials),ue=Object.assign(Object.create(null),ae,{signal:L,method:a.toUpperCase(),headers:Ue(_.normalize()),body:c,duplex:"half",credentials:oe?A:void 0}),f&&(ke.forEach(tn,function(e,t){void 0===ue[t]&&(ue[t]=e);}),void 0===ue.signal&&(ue.signal=null),void 0===ue.body&&(ue.body=null)),0===x&&(ue.redirect="manual",ae&&(ae.redirect="manual")),F=f&&new u(o,ue),e.n=11,f?U(F,ae):U(o,ue);case 11:if(se=e.v,ce=ze.from(se.headers),!C){e.n=12;break}if(!(null!=(fe=ke.toFiniteNumber(ce.getContentLength()))&&fe>T)){e.n=12;break}throw new Ve("maxContentLength size of "+T+" exceeded",Ve.ERR_BAD_RESPONSE,t,F);case 12:return le=y&&("stream"===S||"response"===S),y&&se.body&&(O||C||le&&B)&&(de={},["status","statusText","headers"].forEach(function(e){de[e]=se[e];}),pe=ke.toFiniteNumber(ce.getContentLength()),he=O&&Tt(pe,jt(kt(O),!0))||[],ve=R(he,2),ye=ve[0],be=ve[1],me=function(e){if(C&&e>T)throw new Ve("maxContentLength size of "+T+" exceeded",Ve.ERR_BAD_RESPONSE,t,F);ye&&ye(e);},se=new s(Vt(se.body,65536,me,function(){be&&be(),B&&B();}),de)),S=S||"text",e.n=13,b[ke.findKey(b,S)||"text"](se,t);case 13:if(ge=e.v,!C||y||le){e.n=14;break}if(null!=ge&&("number"==typeof ge.byteLength?we=ge.byteLength:"number"==typeof ge.size?we=ge.size:"string"==typeof ge&&(we="function"==typeof r?(new r).encode(ge).byteLength:ge.length)),!("number"==typeof we&&we>T)){e.n=14;break}throw new Ve("maxContentLength size of "+T+" exceeded",Ve.ERR_BAD_RESPONSE,t,F);case 14:return !le&&B&&B(),e.n=15,new Promise(function(e,n){St(e,n,{data:ge,headers:ze.from(se.headers),status:se.status,statusText:se.statusText,config:t,request:F});});case 15:return e.a(2,e.v);case 16:if(e.p=16,Se=e.v,B&&B(),!(L&&L.aborted&&L.reason instanceof Ve)){e.n=17;break}throw (Oe=L.reason).config=t,F&&(Oe.request=F),Se!==Oe&&Object.defineProperty(Oe,"cause",{__proto__:null,value:Se,writable:!0,enumerable:!1,configurable:!0}),Oe;case 17:if(!q){e.n=18;break}throw F&&!q.request&&(q.request=F),q;case 18:if(!(Se instanceof Ve)){e.n=19;break}throw F&&!Se.request&&(Se.request=F),Se;case 19:if(!Se||"TypeError"!==Se.name||!/Load failed|fetch/i.test(Se.message)){e.n=20;break}throw Ee=new Ve("Network Error",Ve.ERR_NETWORK,t,F,Se&&Se.response),Object.defineProperty(Ee,"cause",{__proto__:null,value:Se.cause||Se,writable:!0,enumerable:!1,configurable:!0}),Ee;case 20:throw Ve.from(Se,Se&&Se.code,t,F,Se&&Se.response);case 21:return e.a(2)}},e,null,[[1,16]])}));return function(t){return e.apply(this,arguments)}}()},cn=new Map,fn=function(e){for(var t,n,r=e&&e.env||{},o=r.fetch,i=[r.Request,r.Response,o],a=i.length,u=cn;a--;)t=i[a],void 0===(n=u.get(t))&&u.set(t,n=a?new Map:sn(r)),u=n;return n};fn();var ln={http:null,xhr:Mt,fetch:{get:fn}};ke.forEach(ln,function(e,t){if(e){try{Object.defineProperty(e,"name",{__proto__:null,value:t});}catch(e){}Object.defineProperty(e,"adapterName",{__proto__:null,value:t});}});var dn=function(e){return "- ".concat(e)},pn=function(e){return ke.isFunction(e)||null===e||!1===e};var hn={getAdapter:function(e,t){for(var n,r,o=(e=ke.isArray(e)?e:[e]).length,i={},a=0;a<o;a++){var u=void 0;if(r=n=e[a],!pn(n)&&void 0===(r=ln[(u=String(n)).toLowerCase()]))throw new Ve("Unknown adapter '".concat(u,"'"));if(r&&(ke.isFunction(r)||(r=r.get(t))))break;i[u||"#"+a]=r;}if(!r){var s=Object.entries(i).map(function(e){var t=R(e,2),n=t[0],r=t[1];return "adapter ".concat(n," ")+(!1===r?"is not supported by the environment":"is not available in the build")}),c=o?s.length>1?"since :\n"+s.map(dn).join("\n"):" "+dn(s[0]):"as no adapter specified";throw new Ve("There is no suitable adapter to dispatch the request "+c,Ve.ERR_NOT_SUPPORT)}return r},adapters:ln};function vn(e){if(e.cancelToken&&e.cancelToken.throwIfRequested(),e.signal&&e.signal.aborted)throw new Rt(null,e)}function yn(e){var t=ke.toSafeFlatObject(e);return vn(t),t.headers=ze.from(ke.getSafeProp(t,"headers")),t.data=Ot.call(t,t.transformRequest),-1!==["post","put","patch"].indexOf(t.method)&&t.headers.setContentType("application/x-www-form-urlencoded",!1),hn.getAdapter(t.adapter||wt.adapter,t)(t).then(function(e){vn(t),t.response=e;try{e.data=Ot.call(t,t.transformResponse,e);}finally{delete t.response;}return e.headers=ze.from(e.headers),e},function(e){if(!Et(e)&&(vn(t),e&&e.response)){t.response=e.response;try{e.response.data=Ot.call(t,t.transformResponse,e.response);}finally{delete t.response;}e.response.headers=ze.from(e.response.headers);}return Promise.reject(e)})}var bn={};["object","boolean","number","function","string","symbol"].forEach(function(e,t){bn[e]=function(n){return P(n)===e||"a"+(t<1?"n ":" ")+e};});var mn={};bn.transitional=function(e,t,n){function r(e,t){return "[Axios v"+en+"] Transitional option '"+e+"'"+t+(n?". "+n:"")}return function(n,o,i){if(!1===e)throw new Ve(r(o," has been removed"+(t?" in "+t:"")),Ve.ERR_DEPRECATED);return t&&!mn[o]&&(mn[o]=!0,console.warn(r(o," has been deprecated since v"+t+" and will be removed in the near future"))),!e||e(n,o,i)}},bn.spelling=function(e){return function(t,n){return console.warn("".concat(n," is likely a misspelling of ").concat(e)),!0}};var gn={assertOptions:function(e,t,n){if("object"!==P(e)||null===e)throw new Ve("options must be an object",Ve.ERR_BAD_OPTION_VALUE);for(var r=Object.keys(e),o=r.length;o-- >0;){var i=r[o],a=Object.prototype.hasOwnProperty.call(t,i)?t[i]:void 0;if(a){var u=e[i],s=void 0===u||a(u,i,e);if(!0!==s)throw new Ve("option "+i+" must be "+s,Ve.ERR_BAD_OPTION_VALUE)}else if(!0!==n)throw new Ve("Unknown option "+i,Ve.ERR_BAD_OPTION)}},validators:bn},wn=gn.validators,On=function(){return l(function e(t){c(this,e),this.defaults=t||{},this.interceptors={request:new ut,response:new ut};},[{key:"request",value:(e=a(g().m(function e(t,n){var r,o,i,a,u,s,c,f;return g().w(function(e){for(;;)switch(e.p=e.n){case 0:return e.p=0,e.n=1,this._request(t,n);case 1:return e.a(2,e.v);case 2:if(e.p=2,(f=e.v)instanceof Error)try{r={},Error.captureStackTrace?Error.captureStackTrace(r):r=new Error,o=r.stack,i="","string"==typeof o&&(a=o.indexOf("\n"),i=-1===a?"":o.slice(a+1)),f.stack?i&&(u=i.indexOf("\n"),s=-1===u?-1:i.indexOf("\n",u+1),c=-1===s?"":i.slice(s+1),String(f.stack).endsWith(c)||(f.stack+="\n"+i)):f.stack=i;}catch(e){}throw f;case 3:return e.a(2)}},e,this,[[0,2]])})),function(t,n){return e.apply(this,arguments)})},{key:"_request",value:function(e,t){var n=this;"string"==typeof e?(t=t||{}).url=e:t=e||{};var r=t=Bt(this.defaults,t),o=r.transitional,i=r.paramsSerializer,a=r.headers;void 0!==o&&gn.assertOptions(o,{silentJSONParsing:wn.transitional(wn.boolean),forcedJSONParsing:wn.transitional(wn.boolean),clarifyTimeoutError:wn.transitional(wn.boolean),legacyInterceptorReqResOrdering:wn.transitional(wn.boolean),advertiseZstdAcceptEncoding:wn.transitional(wn.boolean),validateStatusUndefinedResolves:wn.transitional(wn.boolean)},!1),null!=i&&(ke.isFunction(i)?t.paramsSerializer={serialize:i}:gn.assertOptions(i,{encode:wn.function,serialize:wn.function},!0)),void 0!==t.allowAbsoluteUrls||(void 0!==this.defaults.allowAbsoluteUrls?t.allowAbsoluteUrls=this.defaults.allowAbsoluteUrls:t.allowAbsoluteUrls=!0),gn.assertOptions(t,{baseUrl:wn.spelling("baseURL"),withXsrfToken:wn.spelling("withXSRFToken")},!0),t.method=(ke.getSafeProp(t,"method")||ke.getSafeProp(this.defaults,"method")||"get").toLowerCase();var u=a&&ke.merge(a.common,a[t.method]);a&&ke.forEach(mt.concat("common"),function(e){delete a[e];}),t.headers=ze.concat(u,a);var s=[],c=!0;this.interceptors.request.forEach(function(e){if("function"!=typeof e.runWhen||!1!==e.runWhen(t)){c=c&&e.synchronous;var n=t.transitional||st;n&&n.legacyInterceptorReqResOrdering?s.unshift(e.fulfilled,e.rejected):s.push(e.fulfilled,e.rejected);}});var f,l=[];this.interceptors.response.forEach(function(e){l.push(e.fulfilled,e.rejected);});var d,p=0;if(!c){var h=[yn.bind(this),void 0];for(h.unshift.apply(h,s),h.push.apply(h,l),d=h.length,f=Promise.resolve(t);p<d;)f=f.then(h[p++],h[p++]);return f}d=s.length;for(var v=t;p<d;){var y=s[p++],b=s[p++];try{v=y?y(v):v;}catch(e){if(!b){f=Promise.reject(e);break}try{var m=b.call(this,e);ke.isThenable(m)&&(f=Promise.resolve(m).then(function(){return yn.call(n,v)}));}catch(e){f=Promise.reject(e);}break}}if(!f)try{f=yn.call(this,v);}catch(e){f=Promise.reject(e);}for(p=0,d=l.length;p<d;)f=f.then(l[p++],l[p++]);return f}},{key:"getUri",value:function(e){return nt(Lt((e=Bt(this.defaults,e)).baseURL,e.url,e.allowAbsoluteUrls,e),e.params,e.paramsSerializer)}}]);var e;}();ke.forEach(["delete","get","head","options"],function(e){On.prototype[e]=function(t,n){return this.request(Bt(n||{},{method:e,url:t,data:n&&ke.hasOwnProp(n,"data")?n.data:void 0}))};}),ke.forEach(["post","put","patch","query"],function(e){function t(t){return function(n,r,o){return this.request(Bt(o||{},{method:e,headers:t?{"Content-Type":"multipart/form-data"}:{},url:n,data:r}))}}On.prototype[e]=t(),"query"!==e&&(On.prototype[e+"Form"]=t(!0));});var En=function(){function e(t){if(c(this,e),"function"!=typeof t)throw new TypeError("executor must be a function.");var n;this.promise=new Promise(function(e){n=e;});var r=this;this.promise.then(function(e){if(r._listeners){for(var t=r._listeners.length;t-- >0;)r._listeners[t](e);r._listeners=null;}}),this.promise.then=function(e){var t,n=new Promise(function(e){r.subscribe(e),t=e;}).then(e);return n.cancel=function(){r.unsubscribe(t);},n},t(function(e,t,o){r.reason||(r.reason=new Rt(e,t,o),n(r.reason));});}return l(e,[{key:"throwIfRequested",value:function(){if(this.reason)throw this.reason}},{key:"subscribe",value:function(e){this.reason?e(this.reason):this._listeners?this._listeners.push(e):this._listeners=[e];}},{key:"unsubscribe",value:function(e){if(this._listeners){var t=this._listeners.indexOf(e);-1!==t&&this._listeners.splice(t,1);}}},{key:"toAbortSignal",value:function(){var e=this,t=new AbortController,n=function(e){t.abort(e);};return this.subscribe(n),t.signal.unsubscribe=function(){return e.unsubscribe(n)},t.signal}}],[{key:"source",value:function(){var t;return {token:new e(function(e){t=e;}),cancel:t}}}])}();var Rn={Continue:100,SwitchingProtocols:101,Processing:102,EarlyHints:103,Ok:200,Created:201,Accepted:202,NonAuthoritativeInformation:203,NoContent:204,ResetContent:205,PartialContent:206,MultiStatus:207,AlreadyReported:208,ImUsed:226,MultipleChoices:300,MovedPermanently:301,Found:302,SeeOther:303,NotModified:304,UseProxy:305,Unused:306,TemporaryRedirect:307,PermanentRedirect:308,BadRequest:400,Unauthorized:401,PaymentRequired:402,Forbidden:403,NotFound:404,MethodNotAllowed:405,NotAcceptable:406,ProxyAuthenticationRequired:407,RequestTimeout:408,Conflict:409,Gone:410,LengthRequired:411,PreconditionFailed:412,PayloadTooLarge:413,ContentTooLarge:413,UriTooLong:414,UnsupportedMediaType:415,RangeNotSatisfiable:416,ExpectationFailed:417,ImATeapot:418,MisdirectedRequest:421,UnprocessableEntity:422,UnprocessableContent:422,Locked:423,FailedDependency:424,TooEarly:425,UpgradeRequired:426,PreconditionRequired:428,TooManyRequests:429,RequestHeaderFieldsTooLarge:431,UnavailableForLegalReasons:451,InternalServerError:500,NotImplemented:501,BadGateway:502,ServiceUnavailable:503,GatewayTimeout:504,HttpVersionNotSupported:505,VariantAlsoNegotiates:506,InsufficientStorage:507,LoopDetected:508,NotExtended:510,NetworkAuthenticationRequired:511,WebServerReturnsAnUnknownError:520,WebServerIsDown:521,ConnectionTimedOut:522,OriginIsUnreachable:523,TimeoutOccurred:524,SslHandshakeFailed:525,InvalidSslCertificate:526};Object.entries(Rn).forEach(function(e){var t=R(e,2),n=t[0],r=t[1];void 0===Rn[r]&&(Rn[r]=n);});var Sn=function e(t){var n=new On(t),r=x(On.prototype.request,n);return ke.extend(r,On.prototype,n,{allOwnKeys:!0}),ke.extend(r,n,null,{allOwnKeys:!0}),r.create=function(n){return e(Bt(t,n))},r}(wt);return Sn.Axios=On,Sn.CanceledError=Rt,Sn.CancelToken=En,Sn.isCancel=Et,Sn.VERSION=en,Sn.toFormData=Qe,Sn.AxiosError=Ve,Sn.Cancel=Sn.CanceledError,Sn.all=function(e){return Promise.all(e)},Sn.spread=function(e){return function(t){return e.apply(null,t)}},Sn.isAxiosError=function(e){return ke.isObject(e)&&!0===e.isAxiosError},Sn.mergeConfig=Bt,Sn.AxiosHeaders=ze,Sn.formToJSON=function(e){return bt(ke.isHTMLForm(e)?new FormData(e):e)},Sn.getAdapter=hn.getAdapter,Sn.HttpStatusCode=Rn,Sn.default=Sn,Sn});





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
