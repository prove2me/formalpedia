-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:21.157015+00:00
-- url     : https://prove2.me/theorems/a56711f2-d273-4919-bcea-3e25b28ab987
-- title:
--   Exists Ne Zero Is Standard Smooth Of Relative Dimension
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Is Standard Smooth Of Relative Dimension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
section Null
variable {d : ℕ}
end Null
section Algebra
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
end Algebra
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
section Cover
variable {ι : Type*} [Countable ι] {E H M : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℂ (E i) (H i)} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]
end Cover
section Immersion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}
end Immersion
end GlobalTheory.AffinePoints


