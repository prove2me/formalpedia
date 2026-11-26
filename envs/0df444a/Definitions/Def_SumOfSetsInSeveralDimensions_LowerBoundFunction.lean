-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
-- name    : SumOfSetsInSeveralDimensions_LowerBoundFunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:04.908797+00:00
-- url     : https://prove2.me/theorems/6f6aadb9-b3a6-5f11-8fa7-71fb23e2d4c3
-- title:
--   Lower Bound Function
-- statement:
--   Definitions and structural lemmas for Lower Bound Function, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
def sumsetCardLowerBound (d m n : ℕ) : ℕ :=
  n + ∑ t ∈ Icc 1 (m - 1), min d (n - t)
end SumOfSetsInSeveralDimensions


