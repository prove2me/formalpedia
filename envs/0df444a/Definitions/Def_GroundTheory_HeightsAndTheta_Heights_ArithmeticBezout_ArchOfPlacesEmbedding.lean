-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:44.305469+00:00
-- url     : https://prove2.me/theorems/30b86f4e-3610-42bf-95a7-5d5d84b3e930
-- title:
--   Arch Of Places Embedding
-- statement:
--   Definitions and structural lemmas for Arch Of Places Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace ChowHeightCycleEq
variable {n e : ℕ}
def conjNorm (h : HermNorm n) : HermNorm n where
  mat := h.mat.map (starRingEnd ℂ)
  isUnit_det := by
    rw [show h.mat.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix h.mat from rfl,
      ← RingHom.map_det]
    exact h.isUnit_det.map _
open Matrix in
theorem conjNorm_norm_star (h : HermNorm n) (u : Fin n → ℂ) :
    (conjNorm h).norm (star u) = h.norm u := by
  unfold HermNorm.norm conjNorm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((h.mat.map (starRingEnd ℂ)) *ᵥ star u) i = starRingEnd ℂ ((h.mat *ᵥ u) i) := by
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [this, Complex.norm_conj]
open Classical in

def archOfPlaces {K : Type} [Field K] [NumberField K] (N : InfinitePlace K → HermNorm n)
    (hN : ∀ w : InfinitePlace K, w.IsReal → ∀ u, (N w).norm (star u) = (N w).norm u) :
    ArchData K n where
  normAt σ := if σ = (InfinitePlace.mk σ).embedding then N (InfinitePlace.mk σ)
    else conjNorm (N (InfinitePlace.mk σ))
  conj_norm σ u := by
    simp only [InfinitePlace.mk_conjugate_eq]
    have hreal : ComplexEmbedding.conjugate σ = σ → (InfinitePlace.mk σ).IsReal := fun h =>
      InfinitePlace.isReal_mk_iff.mpr (ComplexEmbedding.isReal_iff.mpr h)
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · by_cases hc : ComplexEmbedding.conjugate σ = (InfinitePlace.mk σ).embedding
      · rw [if_pos hc, if_pos h.symm]
        exact hN _ (hreal (hc.trans h)) u
      · rw [if_neg hc, if_pos h.symm]
        exact conjNorm_norm_star _ u
    · by_cases hs : σ = (InfinitePlace.mk σ).embedding
      · rw [if_pos h.symm, if_pos hs]
        exact hN _ (hreal (h.symm.trans hs.symm)) u
      · rw [if_pos h.symm, if_neg hs, ← conjNorm_norm_star (N _) (star u), star_star]
def meanShift {K : Type} [Field K] (S : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) : ℝ :=
  ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (e + 1)) (map σ P) -
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw 1 (e + 1)) (map σ P)
end ChowHeightCycleEq
end
end GroundTheory.Heights₂.Heights


