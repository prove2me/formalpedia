-- Prove2me | solution 1 for AutomorphicForm.integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/058a12aa-96b7-5f54-9aec-3e2bdf0a7508

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

import Theorems.Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped NNReal

namespace S3Kit

theorem measurable_majorant (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) :
    Measurable (fun g : AdelicGL2 (𝓞 K) K => ‖φ g‖ +
      ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) := by
  refine hφ.norm.measurable.add ?_
  haveI : Countable K :=
    Countable.of_equiv (Fin (Module.finrank ℚ K) → ℚ) (Module.finBasis ℚ K).equivFun.symm.toEquiv
  have hterm : ∀ ξ : K, Measurable fun g : AdelicGL2 (𝓞 K) K =>
      ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖₊ :=
    fun ξ => (hφ.comp (continuous_mul_left _)).nnnorm.measurable
  have h := (Measurable.nnreal_tsum hterm).coe_nnreal_real
  have hfun : (fun g : AdelicGL2 (𝓞 K) K =>
      ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) =
      fun g => ((∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖₊ : ℝ≥0) : ℝ) := by
    funext g
    rw [NNReal.coe_tsum]
    simp only [coe_nnnorm]
  rw [hfun]
  exact h

end S3Kit

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (_hc : 0 < c) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (_h𝓕m : MeasurableSet 𝓕)
    (t : AdelicGL2 (𝓞 K) K) (w : ℝ) (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxc : Continuous x)
    (_hdecay : ∀ N : ℕ, IntegrableOn (fun g : AdelicGL2 (𝓞 K) K => ‖x g‖ * ‖x g‖ *
        (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 K) K))
    (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 K) K → ℂ) (_hφc : Continuous φ) (Cφ : ℝ)
    (_hCφ : ∀ g : AdelicGL2 (𝓞 K) K, ‖φ g‖ ≤ Cφ * adelicHeight K g ^ (s.re + 1 / 2))
    (_hsum : ∀ g : AdelicGL2 (𝓞 K) K, Summable (fun ξ : K =>
      ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖)) :
    IntegrableOn (fun g : AdelicGL2 (𝓞 K) K => ‖x g‖ ^ 2 * (‖φ g‖ + ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨CE, hCE⟩ := AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet K
    c u d₁ d₂ _hc t s.re _hs
  set p : ℝ := s.re + 1 / 2 with hp
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  set N : ℕ := ⌈p⌉₊ with hNceil
  have hpN : p ≤ (N : ℝ) := Nat.le_ceil p
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = max Cφ 0 * max CE 0 := ⟨_, rfl⟩
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀]; exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hdom : ∀ g ∈ 𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁ d₂,
      ‖‖x g‖ ^ 2 * (‖φ g‖ + ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)‖ ≤
      C₀ * (‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) := by
    rintro g ⟨-, s₀, _hs₀, rfl⟩
    obtain ⟨hsumE, hEle⟩ := hCE s₀ _hs₀
    have hwt : 0 ≤ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w) :=
      Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
    have _hCφ' : ∀ g, ‖φ g‖ ≤ max Cφ 0 * adelicHeight K g ^ p := fun g =>
      (_hCφ g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (adelicHeight_pos g).le _))
    have hmajle : ‖φ (s₀ * t)‖ + ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t))‖ ≤
        max Cφ 0 * (adelicHeight K (s₀ * t) ^ p + ∑' ξ : K, adelicHeight K (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t)) ^ p) := by
      rw [mul_add, ← tsum_mul_left]
      refine add_le_add (_hCφ' _) ?_
      exact Summable.tsum_le_tsum (fun ξ => _hCφ' _) (_hsum _) (hsumE.mul_left _)
    have hEle' : adelicHeight K (s₀ * t) ^ p + ∑' ξ : K, adelicHeight K (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t)) ^ p ≤
        max CE 0 * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N := by
      refine hEle.trans ?_
      have hH0 : 0 ≤ archHeight K (glArch (𝓞 K) K s₀) := (archHeight_pos K _).le
      have h1 : archHeight K (glArch (𝓞 K) K s₀) ^ p ≤ (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ (N : ℝ) :=
        (Real.rpow_le_rpow hH0 (by linarith) hp0).trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hpN)
      rw [Real.rpow_natCast] at h1
      calc CE * archHeight K (glArch (𝓞 K) K s₀) ^ p
          ≤ max CE 0 * archHeight K (glArch (𝓞 K) K s₀) ^ p :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hH0 _)
        _ ≤ max CE 0 * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N :=
            mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    have hmaj0 : 0 ≤ ‖φ (s₀ * t)‖ + ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t))‖ :=
      add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
    rw [mul_inv_cancel_right, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hmaj0) hwt), sq]
    have hxx : 0 ≤ ‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ * (‖φ (s₀ * t)‖ + ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t))‖) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w)
        ≤ ‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ * (max Cφ 0 * (max CE 0 * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N)) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hxx) hwt
            exact hmajle.trans (mul_le_mul_of_nonneg_left hEle' (le_max_right _ _))
      _ = C₀ * (‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w)) := by
            rw [hC₀]; ring
  have hbd := (_hdecay N).const_mul C₀
  have hmeasPiece : MeasurableSet (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁ d₂) :=
    _h𝓕m.inter ((Homeomorph.mulRight t).measurableEmbedding.measurableSet_image.mpr
      (measurableSet_centreCutSiegelSet c u d₁ d₂))
  refine Integrable.mono' hbd ?_ ?_
  · have hwtc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) :=
      (NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const fun g =>
        Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
    exact (((_hxc.norm.pow 2).measurable.mul (S3Kit.measurable_majorant K φ _hφc)).mul
      hwtc.measurable).aestronglyMeasurable
  · exact (ae_restrict_iff' hmeasPiece).mpr (Filter.Eventually.of_forall hdom)

end S_AutomorphicForm_integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet (solution)
