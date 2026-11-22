-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
-- name    : LeanPool_CircuitComplexity_AON_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:56.852802+00:00
-- url     : https://prove2.me/theorems/cc28fbd9-5a83-4ce5-a99e-5beb1552b97a
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
inductive AONOp where
  | and
  | or
  deriving Repr, DecidableEq
def AONOp.eval : (op : AONOp) → (n : Nat) → BitString n → Bool
  | .and, n, inputs => Fin.foldl n (fun acc i => acc && inputs i) true
  | .or, n, inputs => Fin.foldl n (fun acc i => acc || inputs i) false
def Basis.unboundedAON : Basis where
  Op := AONOp
  arity
    | .and => .unbounded
    | .or => .unbounded
  eval op n _ inputs := op.eval n inputs
def Basis.boundedAON (k : Nat) : Basis where
  Op := AONOp
  arity
    | .and => .upto k
    | .or => .upto k
  eval op n _ inputs := op.eval n inputs
def Basis.andOr2 : Basis where
  Op := AONOp
  arity _ := .exactly 2
  eval op n _ inputs := op.eval n inputs
end CircuitComplexity


