-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism
-- name    : LeanPool_CircuitComplexity_Nondeterminism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:14:25.805808+00:00
-- url     : https://prove2.me/theorems/ac0e2e32-0e58-4840-bbf4-105ffa75ebd6
-- title:
--   Nondeterminism
-- statement:
--   Definitions and structural lemmas for Nondeterminism, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
variable {k m : Nat}
instance instNeZeroAddLeft [NeZero m] : NeZero (k + m) :=
  ⟨by have := NeZero.ne m; omega⟩
end CircuitComplexity


