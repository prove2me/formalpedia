-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Valiant
-- name    : LeanPool_CircuitComplexity_Valiant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:09:12.566974+00:00
-- url     : https://prove2.me/theorems/dbc74d9d-52a5-4ee8-a983-5082c3461aba
-- title:
--   Valiant
-- statement:
--   Definitions and structural lemmas for Valiant, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Valiant.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity.Valiant
open Digraph
end CircuitComplexity.Valiant


