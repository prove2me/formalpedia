-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
-- name    : SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:06:06.671794+00:00
-- url     : https://prove2.me/theorems/ac1c78a3-055e-5979-bc9c-9218d29aa8e0
-- title:
--   Freiman Dimension Sumset Bounds
-- statement:
--   Definitions and structural lemmas for Freiman Dimension Sumset Bounds, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
end
end SumOfSetsInSeveralDimensions


