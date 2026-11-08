-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:20:44.690746+00:00
-- url     : https://prove2.me/theorems/71bfca1b-d08d-43da-b9da-fbe72068ea6e
-- title:
--   LPSOriginal Reciprocal Numerator
-- statement:
--   Definitions and structural lemmas for LPSOriginal Reciprocal Numerator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNumerator.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDelta_j_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubePower_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_cusp_bounded
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_upstairs_holomorphic

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
def lpsOriginalReciprocalClearedRepresentative
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (k : ℕ) :
    LPSOriginalFilledMeromorphicFunctionRing N hN :=
  (⟨lpsOriginalFilledJ N, lpsOriginalFilledChartMeromorphic_j N hN⟩ :
    LPSOriginalFilledMeromorphicFunctionRing N hN)^k *
    ⟨lpsOriginalNormalizedFilledFunction N hN F,
      lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF⟩
lemma lpsOriginalReciprocalClearedRepresentative_cusp_bounded
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ) (ρ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      ModularForm.discriminant τ^k *
      lpsOriginalNormalizedFilledFunction N hN
        (lpsOriginalReciprocalClearedRepresentative N hN F hF k).val
        (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  have he := lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
    N hN ρ G.val G.property
  have hmult : (fun τ : ℍ => ModularForm.discriminant τ^k *
      lpsOriginalNormalizedFilledFunction N hN G.val
        (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) =ᶠ[UpperHalfPlane.atImInfty]
      (fun τ : ℍ => (ModularForm.E₄ τ^3)^k *
        lpsOriginalNormalizedFilledFunction N hN F
          (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
    filter_upwards [he] with τ hτ
    rw [hτ]
    change ModularForm.discriminant τ^k *
      (lpsOriginalFilledJ N (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)^k *
        lpsOriginalNormalizedFilledFunction N hN F
          (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) = _
    rw [lpsOriginalFilledJ_projection,
      lpsOriginalJInvariant_SL_invariant _ ⟨ρ,rfl⟩ τ, ←mul_assoc,
      lpsOriginalDelta_j_power]
  have hd : UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => (ModularForm.E₄ τ^3)^k) := by
    have hfun : (lpsOriginalE4CubePower k : ℍ → ℂ) =
        (fun τ : ℍ => (ModularForm.E₄ τ^3)^k) :=
      funext (lpsOriginalE4CubePower_apply k)
    rw [←hfun]
    exact ModularFormClass.bdd_at_infty (lpsOriginalE4CubePower k)
  have hf := lpsOriginalNormalizedFilledFunction_cusp_bounded N hN F hF hc ρ
  exact (BoundedAtFilter.mul hd hf).congr' hmult.symm (Filter.EventuallyEq.refl _ _)
def lpsOriginalReciprocalNumeratorModularForm
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ)
    (hi : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt
          ((lpsOriginalReciprocalClearedRepresentative N hN F hF k).val ∘
            (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    LPSOriginalMeromorphicLevelForm N k :=
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  lpsOriginalFilledFunctionDeltaModularForm N
    (lpsOriginalNormalizedFilledFunction N hN G.val) k
    (lpsOriginalNormalizedFilledFunction_upstairs_holomorphic N hN G.val G.property hi)
    (lpsOriginalReciprocalClearedRepresentative_cusp_bounded N hN F hF hc k)
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
def lpsOriginalDeltaHolomorphic : R :=
  ⟨ModularForm.discriminant, ModularFormClass.holo CuspForm.discriminant⟩
end
end QEC.Coding.TannerLiftedProduct


