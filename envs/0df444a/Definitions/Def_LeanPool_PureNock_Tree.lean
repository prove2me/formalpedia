-- Prove2me | Definitions.Def_LeanPool_PureNock_Tree
-- name    : LeanPool_PureNock_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:58:52.178895+00:00
-- url     : https://prove2.me/theorems/5d08b2d0-0ff9-4f12-8644-bd086026882a
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean

module
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
inductive Noun where
  | atom : Nat → Noun
  | cell : Noun → Noun → Noun
deriving Repr, DecidableEq, Inhabited
namespace Noun
def isCell : Noun → Bool
  | .cell _ _ => true
  | .atom _   => false
def isAtom (n : Noun) : Bool := !n.isCell
def leaves : Noun → Nat
  | .atom _   => 1
  | .cell l r => l.leaves + r.leaves
def size : Noun → Nat
  | .atom _   => 1
  | .cell l r => 1 + l.size + r.size
def internal : Noun → Nat
  | .atom _   => 0
  | .cell l r => 1 + l.internal + r.internal
end Noun
inductive NAryTree (k : Nat) where
  | leaf : NAryTree k
  | node : (Fin k → NAryTree k) → NAryTree k
namespace NAryTree
def childi {k : Nat} (i : Fin k) : NAryTree k → Option (NAryTree k)
  | .leaf   => none
  | .node f => some (f i)
end NAryTree
end Nock


