-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
-- name    : SumOfSetsInSeveralDimensions_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:53.563577+00:00
-- url     : https://prove2.me/theorems/11d2e6d8-6a7f-47c3-8654-1ac4735fae69
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
end SumOfSetsInSeveralDimensions


