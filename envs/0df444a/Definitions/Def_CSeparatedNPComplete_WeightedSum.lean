-- Prove2me | Definitions.Def_CSeparatedNPComplete_WeightedSum
-- name    : CSeparatedNPComplete_WeightedSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:45:34.817187+00:00
-- url     : https://prove2.me/theorems/f6f2c68f-ab64-4d33-a83e-4ffc9f1b4bea
-- title:
--   Weighted Sum
-- statement:
--   Definitions and structural lemmas for Weighted Sum, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/WeightedSum.lean

module
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CSeparatedNPComplete
open scoped BigOperators
def extendFin {n : ℕ} (a : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then a ⟨i, h⟩ else 0
end CSeparatedNPComplete


