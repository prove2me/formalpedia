-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
-- name    : SumOfSetsInSeveralDimensions_AffineDim
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:06.094953+00:00
-- url     : https://prove2.me/theorems/a85a515f-23ac-4380-9dbc-d25a43e772b8
-- title:
--   Affine Dim
-- statement:
--   Definitions and structural lemmas for Affine Dim, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Finset
open scoped Pointwise
variable {D : ℕ}
noncomputable def affineDim (S : Finset (Fin D → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (S : Set (Fin D → ℝ))).direction
end Finset


