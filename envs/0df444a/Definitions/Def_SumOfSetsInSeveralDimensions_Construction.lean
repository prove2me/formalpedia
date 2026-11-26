-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_Construction
-- name    : SumOfSetsInSeveralDimensions_Construction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:06:16.451742+00:00
-- url     : https://prove2.me/theorems/6da375bd-8624-4278-aa90-9b5a8b38cf75
-- title:
--   Construction
-- statement:
--   Definitions and structural lemmas for Construction, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}
noncomputable def axisPoints (e k : ℕ) : Finset (Fin (e + 1) → ℝ) :=
  (range (k + 1)).image fun i : ℕ ↦ Pi.single 0 (i : ℝ)
noncomputable def unitVectors (e c : ℕ) : Finset (Fin (e + 1) → ℝ) :=
  ({j : Fin e | (j : ℕ) < c} : Finset (Fin e)).image fun j ↦ Pi.single j.succ 1
noncomputable def axisUnionBasis (e k c : ℕ) : Finset (Fin (e + 1) → ℝ) :=
  axisPoints e k ∪ unitVectors e c
end SumOfSetsInSeveralDimensions


