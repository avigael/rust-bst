/*
 * Binary Search Tree
 */

#![allow(unused_must_use)]
#![allow(dead_code)]
#![allow(unused_imports)]
#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::fmt::Debug;
use std::iter::{FromIterator, IntoIterator};
use std::ops::{Bound, Index, IndexMut, RangeBounds};
use std::mem;

/// Type of BST nodes.
#[derive(Debug)]
struct Node<K, V> {
    key: K,
    val: V,
    size: usize,
    lt: TreeMap<K, V>,
    rt: TreeMap<K, V>,
}

/// Type of BSTs.
#[derive(Debug, Default)]
pub struct TreeMap<K, V> {
    inner: Option<Box<Node<K, V>>>,
}

/// Basic operations and traits
impl<K, V> TreeMap<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    /// Make a new `TreeMap`.
    pub fn new() -> Self {
        TreeMap { inner: None }
    }

    /// Clear a `TreeMap`.
    pub fn clear(&mut self) {
        self.inner = None;
    }

    /// Check if a `TreeMap` is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_none()
    }

    /// Compute the size of a `TreeMap`.
    pub fn len(&self) -> usize {
        match self.inner {
            Some(ref node) => node.size,
            None => 0,
        }
    }

    /// Check if a `TreeMap` has a certain key.
    pub fn has_key(&self, key: &K) -> bool {
        // "tree" intitially set as self but will be used to traverse the tree
        let mut tree = &self.inner;
        loop {
            match tree {
                // Traverses lt/rt until end of BST is reach or keys match
                Some(ref node) => {
                    if &node.key == key {
                        return true;
                    } else if &node.key < key {
                        tree = &node.rt.inner;
                    } else {
                        tree = &node.lt.inner;
                    }
                }
                None => return false,
            }
        }
    }

    /// Get a reference to the value associated with a key, if present.
    ///
    /// If the key is not in the map, return `None`.
    pub fn get(&self, key: &K) -> Option<&V> {
        // "tree" intitially set as self but will be used to traverse the tree
        let mut tree = &self.inner;
        loop {
            match tree {
                // Traverses lt/rt until end of BST is reach or keys match
                Some(node) => {
                    if &node.key == key {
                        return Some(&node.val);
                    } else if &node.key < key {
                        tree = &node.rt.inner;
                    } else {
                        tree = &node.lt.inner;
                    }
                }
                None => return None,
            }
        }
    }

    /// Get a mutable reference to the value associated with a key, if present.
    ///
    /// If the key is not in the map, return `None`.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        // "tree" intitially set as self but will be used to traverse the tree
        let mut tree = &mut self.inner;
        loop {
            match tree {
                Some(ref mut node) => {
                    // Traverses lt/rt until end of BST is reach or keys match
                    if &node.key == key {
                        return Some(&mut node.val);
                    } else if &node.key < key {
                        tree = &mut node.rt.inner;
                    } else {
                        tree = &mut node.lt.inner;
                    }
                }
                None => return None,
            }
        }
    }

    /// Insert a (key, value) pair into a TreeMap.
    ///
    /// If the key is already present in the map, return the previous value and replace the old
    /// value with the new value. Otherwise, insert the new (key, value) pair and return `None`.
    pub fn insert(&mut self, key: K, val: V) -> Option<V> {
        // Checks to see if key already exist in the tree
        if self.has_key(&key) {
            // If so replace the val and return the old value
            // This is done because of the way I set the size of the tree
            let prev = mem::replace(self.get_mut(&key).take().unwrap(), val);
            return Some(prev);
        }
        // "tree" intitially set as self but will be used to traverse the tree
        let mut tree = &mut self.inner;
        loop {
            match tree {
                Some(ref mut node) => {
                    // Traverses lt/rt until end of BST is reach or keys match
                    if node.key < key {
                        // Bececause we are adding a new node we increase by one
                        node.size += 1;
                        tree = &mut node.rt.inner;
                    } else {
                        node.size += 1;
                        tree = &mut node.lt.inner;
                    }
                }
                None => {
                    // Once the end of the tree is reached we add our new node
                    mem::replace(
                        tree,
                        Some(Box::new(Node {
                            key,
                            val,
                            size: 1,
                            lt: TreeMap { inner: None },
                            rt: TreeMap { inner: None },
                        })),
                    );
                    return None;
                }
            }
        }
    }

    /// Insert a nonempty `TreeMap` into a `TreeMap`.
    fn insert_tree(&mut self, other: &mut Self) {
        // "tree" intitially set as self but will be used to traverse the tree
        let mut tree = &mut self.inner;
        loop {
            match tree {
                Some(ref mut node) => {
                    // Checks if other is empty
                    match other.inner {
                        Some(ref mut othr) => {
                            // Traverses lt/rt until end of BST is reach or keys match
                            // Size of other is added to the current tree
                            if node.key < othr.key {
                                node.size += othr.size;
                                tree = &mut node.rt.inner;
                            } else {
                                node.size += othr.size;
                                tree = &mut node.lt.inner;
                            }
                        }
                        None => break,
                    }
                }
                None => {
                    // Once we reach the end of the tree we add our other
                    mem::replace(tree, other.inner.take());
                    break;
                }
            }
        }
    }

    /// Remove a key from a `TreeMap`.
    ///
    /// If the map contains the key, remove the key and return the associated value.
    /// If the map does not contain the key, return None and leave the map unchanged.
    pub fn remove(&mut self, key: K) -> Option<V> {
        // Checks if the key does not exist inside the tree
        if !self.has_key(&key) {
            return None;
        }
        // "tree" intitially set as self but will be used to traverse the tree
        let mut tree = self;
        loop {
            let cmp = key.cmp(&tree.inner.as_ref().unwrap().key);
            match cmp {
                // Traverses lt/rt until end of BST is reach or keys match
                // Once the node is found we remove it
                Ordering::Equal => break,
                Ordering::Less => {
                    // Size is decreases because we are removing a node
                    let node = tree.inner.as_mut().unwrap();
                    node.size -= 1;
                    tree = &mut node.lt;
                }
                Ordering::Greater => {
                    let node = tree.inner.as_mut().unwrap();
                    node.size -= 1;
                    tree = &mut node.rt;
                }
            }
        }
        // Once we have found the node we remove it and return the value
        let mut node = tree.inner.take().unwrap();
        tree.inner = node.lt.inner.take();
        tree.insert_tree(&mut node.rt);
        Some(node.val)
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter::new(&self)
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut::new(self)
    }
}

impl<K, V> FromIterator<(K, V)> for TreeMap<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn from_iter<T>(iter: T) -> TreeMap<K, V>
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let mut tree = TreeMap::new();

        for i in iter {
            let (key, val) = i;
            tree.insert(key, val);
        }
        tree
    }
}

/// Now, we will implement two kinds of indexing traits: `Index` and `IndexMut`.
///
/// Rust's built-in syntactic sugar hooks into these traits, for instance we can write stuff like:
///
///
/// > let val = map[idx];
///
///
/// which is short for
///
///
/// > let val = *map.index(idx);
///
///
/// if we have the `Index` trait. If we implement the `IndexMut` trait, we can write stuff like:
///
///
/// > map[idx] = new_val;
///
///
/// which is short for
///
///
/// > *map.index(idx) = new_val;
///
///
/// `Index` returns a reference to the value for a given key, and `IndexMut` returns a mutable
/// reference to the value for a given key. If the key is not in the map, panic. You will probably
/// want to take a look at the documentation for `Index` and `IndexMut`.
///
/// Note: the Rust `BTreeMap` actually has a more general type for these operations, something like:
///
/// > fn index<Q>(&self, key: &Q) -> &V
/// > where
/// >   K: Borrow<Q>,
/// >   Q: Ord + ?Sized,
/// > { ... }
impl<'a, K, V> Index<&'a K> for TreeMap<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    type Output = V;

    fn index(&self, key: &K) -> &V {
        if self.get(&key).is_none() {
            panic!("ERROR: Key not found");
        }
        &self.get(&key).unwrap()
    }
}

impl<'a, K, V> IndexMut<&'a K> for TreeMap<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn index_mut(&mut self, key: &'a K) -> &mut V {
        if self.get(&key).is_none() {
            panic!("ERROR: Key not found");
        }
        self.get_mut(&key).unwrap()
    }
}

/// Iterators
enum Next<I, T> {
    Item(I),
    Tree(T),
}

pub struct IntoIter<K, V> {
    next_nodes: Vec<Next<(K, V), TreeMap<K, V>>>,
    current_val: Option<(K, V)>,
}

impl<K, V> IntoIter<K, V> {
    fn new(tree: TreeMap<K, V>) -> Self {
        let mut var = IntoIter {
            next_nodes: Vec::new(),
            current_val: None,
        };
        var.descend_left(tree);
        var
    }

    fn descend_left(&mut self, tree: TreeMap<K, V>) {
        let mut cur = tree.inner;
        loop {
            match cur {
                Some(node) => {
                    if self.current_val.is_some() {
                        self.next_nodes
                            .push(Next::Item(self.current_val.take().unwrap()));
                    }
                    self.next_nodes.push(Next::Tree(node.rt));
                    self.current_val = Some((node.key, node.val));
                    cur = node.lt.inner;
                }
                None => break,
            }
        }
    }
}

/// `IntoIterator` trait for `TreeMap`.
impl<K, V> IntoIterator for TreeMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter::new(self)
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_val.is_some() {
                return self.current_val.take();
            }
            match self.next_nodes.pop() {
                Some(Next::Tree(tree)) => {
                    if tree.inner.is_none() {
                        continue;
                    } else {
                        IntoIter::descend_left(self, tree);
                    }
                }
                Some(Next::Item(item)) => {
                    return Some(item);
                }
                None => {
                    return None;
                }
            }
        }
    }
}

pub struct Iter<'a, K, V> {
    next_nodes: Vec<Next<(&'a K, &'a V), &'a TreeMap<K, V>>>,
    current_val: Option<(&'a K, &'a V)>,
}

impl<'a, K, V> Iter<'a, K, V> {
    fn new(tree: &'a TreeMap<K, V>) -> Self {
        let mut var = Iter {
            next_nodes: Vec::new(),
            current_val: None,
        };
        var.descend_left(tree);
        var
    }

    fn descend_left(&mut self, tree: &'a TreeMap<K, V>) {
        let mut cur = &tree.inner;
        loop {
            match cur {
                Some(node) => {
                    if self.current_val.is_some() {
                        self.next_nodes
                            .push(Next::Item(self.current_val.take().unwrap()));
                    }
                    self.next_nodes.push(Next::Tree(&node.rt));
                    self.current_val = Some((&node.key, &node.val));
                    cur = &node.lt.inner;
                }
                None => break,
            }
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_val.is_some() {
                return self.current_val.take();
            }
            match self.next_nodes.pop() {
                Some(Next::Tree(tree)) => {
                    if tree.inner.is_none() {
                        continue;
                    } else {
                        Iter::descend_left(self, tree);
                    }
                }
                Some(Next::Item(item)) => {
                    return Some(item);
                }
                None => {
                    return None;
                }
            }
        }
    }
}

pub struct IterMut<'a, K, V> {
    next_nodes: Vec<Next<(&'a K, &'a mut V), &'a mut TreeMap<K, V>>>,
    current_val: Option<(&'a K, &'a mut V)>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    fn new(tree: &'a mut TreeMap<K, V>) -> Self {
        let mut var = IterMut {
            next_nodes: Vec::new(),
            current_val: None,
        };
        var.descend_left(tree);
        var
    }

    fn descend_left(&mut self, tree: &'a mut TreeMap<K, V>) {
        let mut cur = &mut tree.inner;
        loop {
            match cur {
                Some(node) => {
                    if self.current_val.is_some() {
                        self.next_nodes
                            .push(Next::Item(self.current_val.take().unwrap()));
                    }
                    self.next_nodes.push(Next::Tree(&mut node.rt));
                    self.current_val = Some((&node.key, &mut node.val));
                    cur = &mut node.lt.inner;
                }
                None => break,
            }
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_val.is_some() {
                return self.current_val.take();
            }
            match self.next_nodes.pop() {
                Some(Next::Tree(tree)) => {
                    if tree.inner.is_none() {
                        continue;
                    } else {
                        IterMut::descend_left(self, tree);
                    }
                }
                Some(Next::Item(item)) => {
                    return Some(item);
                }
                None => {
                    return None;
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::TreeMap;
    use std::fmt::Debug;

    impl<K, V> TreeMap<K, V>
    where
        K: Ord + Debug,
        V: Debug,
    {
        /// Test function: checks the BST invariant.
        fn is_bst(&self) -> bool {
            let mut lsize = 0;
            let mut rsize = 0;
            if let Some(boxed) = &self.inner {
                let lt = &boxed.lt;
                let rt = &boxed.rt;

                if let Some(lnode) = &lt.inner {
                    if lnode.key >= boxed.key || !lt.is_bst() {
                        return false;
                    }

                    lsize = lnode.size;
                }

                if let Some(rnode) = &rt.inner {
                    if rnode.key <= boxed.key || !rt.is_bst() {
                        return false;
                    }

                    rsize = rnode.size;
                }

                boxed.size == lsize + rsize + 1
            } else {
                true
            }
        }
    }

    #[test]
    fn test_insert() {
        let mut tree = TreeMap::new();

        tree.insert(1, 11);
        tree.insert(3, 33);
        tree.insert(2, 22);

        assert_eq!(tree.get(&1), Some(&11));
        assert_eq!(tree.get(&2), Some(&22));
        assert_eq!(tree.get(&3), Some(&33));

        assert!(tree.is_bst());

        let insert_res = tree.insert(1, 111);

        assert_eq!(tree.get(&1), Some(&111));
        assert_eq!(insert_res, Some(11));
    }

    #[test]
    fn test_clear() {
        let mut tree = TreeMap::new();

        tree.insert(1, 11);
        tree.insert(3, 33);
        tree.insert(2, 22);

        assert_eq!(tree.len(), 3);

        tree.clear();

        assert_eq!(tree.len(), 0);
    }

    #[test]
    fn test_remove() {
        let mut tree = TreeMap::new();

        tree.insert(1, 11);
        tree.insert(3, 33);
        tree.insert(2, 22);

        assert_eq!(tree.remove(1), Some(11));
        assert_eq!(tree.len(), 2);
        assert!(tree.is_bst());

        assert_eq!(tree.remove(1), None);
        assert_eq!(tree.len(), 2);
        assert!(tree.is_bst());
    }

    #[test]
    fn test_mut() {
        let mut tree = TreeMap::new();

        tree.insert(1, 11);
        tree.insert(3, 33);
        tree.insert(2, 22);

        assert_eq!(tree.get(&3), Some(&33));

        *tree.get_mut(&3).unwrap() = 333;

        assert_eq!(tree.get(&3), Some(&333));

        assert!(tree.is_bst());
    }

    #[test]
    fn test_index() {
        let mut tree = TreeMap::new();

        tree.insert(1, 11);
        tree.insert(3, 33);
        tree.insert(2, 22);

        assert_eq!(tree[&1], 11);

        tree[&2] = 22;

        assert_eq!(tree.get(&2), Some(&22));

        assert!(tree.is_bst());
    }

    #[should_panic]
    #[test]
    fn test_bad_index() {
        let mut tree = TreeMap::new();

        tree.insert(1, 11);
        tree.insert(3, 33);
        tree.insert(2, 22);

        tree[&5] = 10;
    }

    #[test]
    fn test_from_iter() {
        let vec = vec![(1, 11), (3, 33), (2, 22)];
        let tree: TreeMap<i32, i32> = vec.into_iter().collect();

        assert!(tree.is_bst());

        assert_eq!(tree.get(&1), Some(&11));
        assert_eq!(tree.get(&2), Some(&22));
        assert_eq!(tree.get(&3), Some(&33));
    }

    #[test]
    fn test_iter() {
        let vec = vec![(1, 11), (3, 33), (2, 22)];
        let tree: TreeMap<i32, i32> = vec.into_iter().collect();

        let mut iter = tree.into_iter();

        assert_eq!(iter.next(), Some((1, 11)));
        assert_eq!(iter.next(), Some((2, 22)));
        assert_eq!(iter.next(), Some((3, 33)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_borrow_iter() {
        let vec = vec![(1, 11), (3, 33), (2, 22)];
        let tree: TreeMap<i32, i32> = vec.into_iter().collect();

        let mut iter = tree.iter();

        assert_eq!(iter.next(), Some((&1, &11)));
        assert_eq!(iter.next(), Some((&2, &22)));
        assert_eq!(iter.next(), Some((&3, &33)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_mut_iter() {
        let vec = vec![(1, 11), (3, 33), (2, 22)];
        let mut tree: TreeMap<i32, i32> = vec.into_iter().collect();

        for (k, v) in tree.iter_mut() {
            *v = k + 100;
        }

        assert!(tree.is_bst());
        assert_eq!(tree.len(), 3);

        assert_eq!(tree.get(&1), Some(&101));
        assert_eq!(tree.get(&2), Some(&102));
        assert_eq!(tree.get(&3), Some(&103));
    }

    use std::cell::RefCell;

    #[derive(Debug)]
    struct MyDropper<'a> {
        inner: String,
        log: &'a RefCell<Vec<String>>,
    }

    impl<'a> Drop for MyDropper<'a> {
        fn drop(&mut self) {
            // Record the dropped String in a shared log
            let newstr = self.inner.clone();
            self.log.borrow_mut().push(newstr);
        }
    }

    #[test]
    fn test_drop() {
        let drops = RefCell::new(vec![]);

        // Contents of tree in pre-order traversal
        let contents = vec![
            String::from("m"),
            String::from("h"),
            String::from("a"),
            String::from("k"),
            String::from("t"),
            String::from("p"),
            String::from("z"),
        ];

        // Set up a complete binary tree (key = val)
        {
            let mut tree = TreeMap::new();
            for s in &contents {
                let log = &drops;
                let key = s.clone();
                let inner = s.clone();
                tree.insert(key, MyDropper { inner, log });
            }
        } // ... and drop it

        // Check the order of drops
        assert_eq!(*drops.borrow(), contents);
    }
}
