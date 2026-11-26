-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
-- name    : SumOfSetsInSeveralDimensions_LowerBoundValues
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:22.079077+00:00
-- url     : https://prove2.me/theorems/1ab2b99d-dfca-5370-b321-3e1ccc5c9cc6
-- title:
--   Lower Bound Values
-- statement:
--   Definitions and structural lemmas for Lower Bound Values, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace SumOfSetsInSeveralDimensions
open Finset
variable {d m n : ℕ}
end SumOfSetsInSeveralDimensions


