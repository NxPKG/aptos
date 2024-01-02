// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! Contains definitions of symbols -- internalized strings which support fast hashing and
//! comparison.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    fmt::{Error, Formatter},
    rc::Rc,
    sync::atomic,
};

/// Representation of a symbol.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Symbol(usize);

impl Symbol {
    pub fn display_user<'a>(&'a self, pool: &'a SymbolPool) -> SymbolDisplay<'a> {
        SymbolDisplay {
            sym: self,
            pool,
            full: false,
        }
    }

    pub fn display<'a>(&'a self, pool: &'a SymbolPool) -> SymbolDisplay<'a> {
        SymbolDisplay {
            sym: self,
            pool,
            full: true,
        }
    }
}

/// A helper to support symbols in formatting.
pub struct SymbolDisplay<'a> {
    sym: &'a Symbol,
    pool: &'a SymbolPool,
    full: bool,
}

impl<'a> fmt::Display for SymbolDisplay<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        if self.full {
            f.write_str(&self.pool.string(*self.sym))
        } else {
            f.write_str(&self.pool.base_string(*self.sym))
        }
    }
}

/// A pool of symbols. Allows to lookup a symbol by a string representation, and discover
/// the string representation of an existing symbol. This struct does not need be mutable
/// for operations on it, which is important so references to it can be freely passed around.
#[derive(Debug)]
pub struct SymbolPool {
    inner: RefCell<InnerPool>,
}

#[derive(Debug)]
struct SymbolRep {
    full: Rc<String>, // Full symbol name
    base: Symbol,     // User-displayed symbol name
    derived_count: atomic::AtomicU64,
}

#[derive(Debug)]
struct InnerPool {
    reps: Vec<SymbolRep>,
    lookup: HashMap<Rc<String>, usize>,
}

impl SymbolPool {
    /// Creates a new SymbolPool.
    pub fn new() -> SymbolPool {
        SymbolPool {
            inner: RefCell::new(InnerPool {
                reps: vec![],
                lookup: HashMap::new(),
            }),
        }
    }

    /// Looks up a symbol by its string representation. If a symbol with this representation
    /// already exists, it will be returned, otherwise a new one will be created in the
    /// pool, with `s` as its own base for presentation to users.
    ///
    /// Note that the implementation uses internally a RefCell for storing symbols, so the pool does
    /// not need to be mutable.
    pub fn make(&self, s: &str) -> Symbol {
        let key = Rc::new(s.to_string());
        {
            if let Some(n) = self.inner.borrow().lookup.get(&key) {
                return Symbol(*n);
            }
        }
        let mut pool = self.inner.borrow_mut();
        // if we had multi-threading, we should double-check for a race here.
        let new_sym = pool.reps.len();
        let sym_rep = SymbolRep {
            full: key.clone(),
            base: Symbol(new_sym),
            derived_count: atomic::AtomicU64::new(0),
        };
        pool.reps.push(sym_rep);
        pool.lookup.insert(key, new_sym);
        Symbol(new_sym)
    }

    /// Looks up a derived symbol by its string representation. If a symbol with this representation
    /// already exists, it will be returned, otherwise a new one will be created in the pool, with.
    /// `base` as its base for presentation to users.
    ///
    /// Note that
    /// implementation uses internally a RefCell for storing symbols, so the pool does not need to
    /// be mutable.
    pub fn make_derived_sym(&self, derived: &str, base: Symbol) -> Symbol {
        let key = Rc::new(derived.to_string());
        {
            if let Some(n) = self.inner.borrow().lookup.get(&key) {
                return Symbol(*n);
            }
        }
        let sym_rep = SymbolRep {
            full: key.clone(),
            base,
            derived_count: atomic::AtomicU64::new(0),
        };
        let mut pool = self.inner.borrow_mut();
        // if we had multi-threading, we should double-check for a race here.
        let new_sym = pool.reps.len();
        pool.reps.push(sym_rep);
        pool.lookup.insert(key, new_sym);
        Symbol(new_sym)
    }

    /// Create a unique name with same base as sym.
    pub fn make_unique(&self, sym: Symbol) -> Symbol {
        let (base_sym, base_string, count) = {
            let inner_ref = self.inner.borrow();
            let sym_rep = &inner_ref.reps[sym.0];
            let base_sym = sym_rep.base;
            let base_rep = &inner_ref.reps[base_sym.0];
            let base_string = base_rep.full.clone();
            let count = base_rep
                .derived_count
                .fetch_add(1, atomic::Ordering::SeqCst);
            (base_sym, base_string, count)
        };
        let unique_string = format!("{}${}$", base_string, count);
        self.make_derived_sym(&unique_string, base_sym)
    }

    /// Create a symbol to represent a local temporary with specified index
    pub fn make_local_sym(&self, idx: usize) -> Symbol {
        let tmp_string = format!("$t{}", idx);
        self.make(&tmp_string)
    }

    /// Returns the string representation of this symbol, as an rc'ed string to avoid copies.
    /// If the passed symbol was not created from this pool, a runtime error may happen (or a wrong
    /// string will be returned).
    pub fn string(&self, sym: Symbol) -> Rc<String> {
        self.inner.borrow().reps[sym.0].full.clone()
    }

    /// Returns the user form of this symbol, as a symbol.
    /// If the passed symbol was not created from this pool, a runtime error may happen (or a wrong
    /// string will be returned).
    pub fn base(&self, sym: Symbol) -> Symbol {
        self.inner.borrow().reps[sym.0].base
    }

    /// Returns the user form of this symbol, as an rc'ed string to avoid copies.
    /// If the passed symbol was not created from this pool, a runtime error may happen (or a wrong
    /// string will be returned).
    pub fn base_string(&self, sym: Symbol) -> Rc<String> {
        self.string(self.base(sym))
    }
}

impl Default for SymbolPool {
    fn default() -> Self {
        Self::new()
    }
}
