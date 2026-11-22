-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Shannon
-- name    : LeanPool_CircuitComplexity_Shannon
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:11:35.346799+00:00
-- url     : https://prove2.me/theorems/f046fbf5-fd9c-40a6-ba7a-809275db2179
-- title:
--   Shannon
-- statement:
--   Definitions and structural lemmas for Shannon, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Shannon.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
end CircuitComplexity


