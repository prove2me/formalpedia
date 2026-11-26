-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
-- name    : SumOfSetsInSeveralDimensions_ClosedForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:06:15.985712+00:00
-- url     : https://prove2.me/theorems/44b779f5-a06a-4e90-adeb-9e2f13eb6fca
-- title:
--   Closed Form
-- statement:
--   Definitions and structural lemmas for Closed Form, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}
end SumOfSetsInSeveralDimensions


