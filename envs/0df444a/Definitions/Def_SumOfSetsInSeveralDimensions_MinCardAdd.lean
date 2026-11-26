-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
-- name    : SumOfSetsInSeveralDimensions_MinCardAdd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:06:45.668808+00:00
-- url     : https://prove2.me/theorems/ad0a8fce-fb1e-4fe4-90d7-1c70b63b92a1
-- title:
--   Min Card Add
-- statement:
--   Definitions and structural lemmas for Min Card Add, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/MinCardAdd.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_Construction
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable def minCardAdd (d m n : ℕ) : ℕ :=
  sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ (A + B).affineDim = d ∧
    #(A + B) = k}
noncomputable def minCardAddOfDimRight (d m n : ℕ) : ℕ :=
  sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ B.affineDim = d ∧ #(A + B) = k}
variable {d m n : ℕ}
end SumOfSetsInSeveralDimensions


