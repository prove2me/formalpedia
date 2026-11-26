-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
-- name    : SumOfSetsInSeveralDimensions_AffineDimSumset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:22.423525+00:00
-- url     : https://prove2.me/theorems/4031710b-7642-5a65-ae14-f60998e88e58
-- title:
--   Affine Dim Sumset
-- statement:
--   Definitions and structural lemmas for Affine Dim Sumset, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Finset
open scoped Pointwise
variable {D : ℕ}
end Finset


