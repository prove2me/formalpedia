-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
-- name    : SumOfSetsInSeveralDimensions_GeometricDeletion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:31.653054+00:00
-- url     : https://prove2.me/theorems/67a11107-3b56-517c-a156-ddbb22e4f2c4
-- title:
--   Geometric Deletion
-- statement:
--   Definitions and structural lemmas for Geometric Deletion, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/GeometricDeletion.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {X Y : Finset (Fin D → ℝ)} {x₀ y₀ : Fin D → ℝ}
noncomputable def deletedComplement (X Y : Finset (Fin D → ℝ)) : Finset (Fin D → ℝ) :=
  (X.erase 0 ∪ Y.erase 0) \ (X.erase 0 + Y.erase 0)
noncomputable def deletedSpan (X Y : Finset (Fin D → ℝ)) : Submodule ℝ (Fin D → ℝ) :=
  vectorSpan ℝ (↑(X.erase 0 + Y.erase 0) : Set (Fin D → ℝ))
end SumOfSetsInSeveralDimensions


