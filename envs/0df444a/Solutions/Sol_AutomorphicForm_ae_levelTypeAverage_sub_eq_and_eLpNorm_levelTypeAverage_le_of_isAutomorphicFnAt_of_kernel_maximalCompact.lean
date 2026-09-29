-- Prove2me | solution 1 for AutomorphicForm.ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3b891fef-be05-5657-a6f7-df736cc9480f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped Pointwise ENNReal
open AutomorphicForm

theorem T6B.enorm_integral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (u f : α → ℂ)
    (hu : AEMeasurable (fun a => ‖u a‖ₑ) μ) (hf : AEMeasurable (fun a => ‖f a‖ₑ) μ) :
    ‖∫ a, u a * f a ∂μ‖ₑ ^ 2 ≤ (∫⁻ a, ‖u a‖ₑ ^ 2 * ‖f a‖ₑ ∂μ) * ∫⁻ a, ‖f a‖ₑ ∂μ := by
  have hhalf : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hhalf' : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  have htwo : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have h1 : ‖∫ a, u a * f a ∂μ‖ₑ ≤ ∫⁻ a, (‖u a‖ₑ * ‖f a‖ₑ ^ (1 / 2 : ℝ)) * ‖f a‖ₑ ^ (1 / 2 : ℝ) ∂μ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun a => ?_))
    rw [enorm_mul, mul_assoc, ← pow_two, hhalf]
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun a => ‖u a‖ₑ * ‖f a‖ₑ ^ (1 / 2 : ℝ)) (g := fun a => ‖f a‖ₑ ^ (1 / 2 : ℝ))
    (hu.mul (hf.pow_const _)) (hf.pow_const _)
  have hA : (∫⁻ a, (‖u a‖ₑ * ‖f a‖ₑ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) = ∫⁻ a, ‖u a‖ₑ ^ 2 * ‖f a‖ₑ ∂μ := by
    refine lintegral_congr fun a => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hhalf', htwo]
  have hB : (∫⁻ a, (‖f a‖ₑ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) = ∫⁻ a, ‖f a‖ₑ ∂μ :=
    lintegral_congr fun a => hhalf' _
  have h3 : ‖∫ a, u a * f a ∂μ‖ₑ ≤
      (∫⁻ a, ‖u a‖ₑ ^ 2 * ‖f a‖ₑ ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, ‖f a‖ₑ ∂μ) ^ (1 / 2 : ℝ) := by
    refine h1.trans ?_
    have h2' := h2
    simp only [Pi.mul_apply] at h2'
    rwa [hA, hB] at h2'
  calc ‖∫ a, u a * f a ∂μ‖ₑ ^ 2
      ≤ ((∫⁻ a, ‖u a‖ₑ ^ 2 * ‖f a‖ₑ ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, ‖f a‖ₑ ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h3 2
    _ = _ := by rw [mul_pow, hhalf, hhalf]

theorem T6B.iSup_ofReal_min_natCast (r : ℝ) (hr : 0 ≤ r) :
    (⨆ n : ℕ, ENNReal.ofReal (min r n)) = ENNReal.ofReal r := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  refine le_iSup_of_le ⌈r⌉₊ ?_
  rw [min_eq_left (Nat.le_ceil r)]

theorem T6B.enorm_integral_mul_sq_le' {α : Type*} [MeasurableSpace α] (μ : Measure α) (u f : α → ℂ)
    (hu : AEStronglyMeasurable u μ) (hf : AEStronglyMeasurable f μ) :
    ‖∫ a, u a * f a ∂μ‖ₑ ^ 2 ≤ (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2) * ‖f a‖ₑ ∂μ) * ∫⁻ a, ‖f a‖ₑ ∂μ := by
  have h := T6B.enorm_integral_mul_sq_le μ u f hu.enorm hf.enorm
  refine h.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun a => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (h : AdelicGL2 (𝓞 K) K) (hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) = 1) :
    ∫⁻ x in Φ, ENNReal.ofReal (‖u (x * h)‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ x in Φ, ENNReal.ofReal (‖u x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := isFiniteMeasure_restrict.2 hΦfin.ne
  have huh : AEStronglyMeasurable (fun x => u (x * h)) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    hu.comp_quasiMeasurePreserving (measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 K) K) h).quasiMeasurePreserving
  have hmeas_min : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∀ n : ℕ, AEStronglyMeasurable (fun x => min (‖v x‖ ^ 2) (n : ℝ))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := fun v hv n =>
    ((continuous_id.pow 2).min continuous_const).comp_aestronglyMeasurable hv.restrict.norm
  have hnn : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ) (n : ℕ) (x : AdelicGL2 (𝓞 K) K), 0 ≤ min (‖v x‖ ^ 2) (n : ℝ) :=
    fun v n x => le_min (sq_nonneg _) (Nat.cast_nonneg n)
  have hint : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∀ n : ℕ, Integrable (fun x => min (‖v x‖ ^ 2) (n : ℝ)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    fun v hv n => Integrable.of_bound (hmeas_min v hv n) n (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn v n x)]; exact min_le_right _ _)

  have key : ∀ n : ℕ, ∫⁻ x in Φ, ENNReal.ofReal (min (‖u (x * h)‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ x in Φ, ENNReal.ofReal (min (‖u x‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro n
    have hB := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
      K α β Φ hΦs hΦ h hh (fun x => ((min (‖u x‖ ^ 2) (n : ℝ) : ℝ) : ℂ)) (fun γ g => by beta_reduce; rw [hΓ γ g])
    beta_reduce at hB
    rw [integral_complex_ofReal, integral_complex_ofReal] at hB
    have hR : ∫ x in Φ, min (‖u (x * h)‖ ^ 2) (n : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ x in Φ, min (‖u x‖ ^ 2) (n : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by exact_mod_cast hB
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _ huh n) (Filter.Eventually.of_forall (hnn _ n)),
      ← ofReal_integral_eq_lintegral_ofReal (hint _ hu n) (Filter.Eventually.of_forall (hnn _ n)), hR]

  have hsup : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∫⁻ x in Φ, ENNReal.ofReal (‖v x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ⨆ n : ℕ, ∫⁻ x in Φ, ENNReal.ofReal (min (‖v x‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro v hv
    rw [← lintegral_iSup' (fun n => (hmeas_min v hv n).aemeasurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => fun a b hab =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hab)))]
    exact lintegral_congr fun x => (T6B.iSup_ofReal_min_natCast _ (sq_nonneg _)).symm
  rw [hsup _ huh, hsup _ hu]
  exact iSup_congr key

namespace Ws35H
namespace PD

theorem pd_main
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
    ∀ (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ) (_hψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ),
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * φ (g * (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), P (φ - ψ) g = P φ g - P ψ g) ∧
    eLpNorm (P φ) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ ENNReal.ofReal (∫ k, ‖κ k‖ ∂(maximalCompactHaar K)) * eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  letI iA : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  intro κ hκ P hP φ ψ hφ hψ
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set D := AutomorphicForm.canonicalTruncationDomain K α β with hD
  set μK := maximalCompactHaar K with hμK
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : μ D < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      D hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne

  have facts : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      AEStronglyMeasurable u μ ∧ MemLp u 2 (μ.restrict D) ∧
      ∀ g : AdelicGL2 (𝓞 K) K, ∫⁻ x in D, ENNReal.ofReal (‖u (x * g)‖ ^ 2) ∂μ =
        ∫⁻ x in D, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
    intro u hu
    have hLs : IsLsXiFunction (𝓞 K) K ⊤ ξK u ∧ MemLp u 2 (μ.restrict D) :=
      (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
    have hΓ := hLs.1.left_invariant
    have hZ := hLs.1.central_transform
    have hmeas : AEStronglyMeasurable u μ :=
      AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ D hslab hFD ξK u hu
    refine ⟨hmeas, hLs.2, fun g => ?_⟩
    have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
      NumberField.TateGlobal.ideleNorm_pos _
    have hr : 0 < 1 / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := one_div_pos.2 hd
    obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.2 hr)
    have hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * g)) = 1 := by
      rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar K, pow_two,
        NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hr.le, one_div_mul_cancel hd.ne']
    have hpt : ∀ x : AdelicGL2 (𝓞 K) K, ‖u (x * (centralScalar (𝓞 K) K z * g))‖ = ‖u (x * g)‖ := by
      intro x
      have hz' : u (centralScalar (𝓞 K) K z * (x * g)) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u (x * g) :=
        hZ ⟨z, Subgroup.mem_top z⟩ (x * g)
      rw [← mul_assoc, mul_centralScalar_comm, mul_assoc, hz', norm_mul, hξu z, one_mul]
    rw [← T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq K α β _ hslab hFD hfin u hmeas hΓ _ hh]
    exact lintegral_congr fun x => by rw [hpt]

  have hκm : AEStronglyMeasurable κ μK := hκ.aestronglyMeasurable
  have hκint : ∫⁻ k, ‖κ k‖ₑ ∂μK < ⊤ := by
    have : Integrable κ μK := hκ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace κ)
    exact this.2

  have hchart_m : Measurable fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) => p.1 * (p.2 : AdelicGL2 (𝓞 K) K) :=
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable
  have hq : Measure.QuasiMeasurePreserving
      (fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) => p.1 * (p.2 : AdelicGL2 (𝓞 K) K))
      ((μ.restrict D).prod μK) μ := by
    refine ⟨hchart_m, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
    rw [Measure.map_apply hchart_m hs, Measure.prod_apply_symm (hchart_m hs)]
    have : ∀ k : ↥(adelicMaximalCompact K),
        (μ.restrict D) ((fun x : AdelicGL2 (𝓞 K) K => (x, k)) ⁻¹'
          ((fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) => p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) ⁻¹' s)) = 0 := by
      intro k
      have hset : ((fun x : AdelicGL2 (𝓞 K) K => (x, k)) ⁻¹'
          ((fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) => p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) ⁻¹' s)) =
          (fun x => x * (k : AdelicGL2 (𝓞 K) K)) ⁻¹' s := rfl
      rw [hset]
      refine le_antisymm ?_ bot_le
      calc (μ.restrict D) ((fun x => x * (k : AdelicGL2 (𝓞 K) K)) ⁻¹' s)
          ≤ μ ((fun x => x * (k : AdelicGL2 (𝓞 K) K)) ⁻¹' s) := Measure.restrict_le_self _
        _ = μ s := measure_preimage_mul_right μ _ s
        _ = 0 := h0
    simp only [this, lintegral_zero]

  have hjoint : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, AEStronglyMeasurable u μ →
      AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) => u (p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))
        ((μ.restrict D).prod μK) := fun u hu => hu.comp_quasiMeasurePreserving hq
  have hsect : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, AEStronglyMeasurable u μ →
      ∀ᵐ x ∂(μ.restrict D), AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => u (x * (k : AdelicGL2 (𝓞 K) K))) μK :=
    fun u hu => (hjoint u hu).prodMk_left

  have hsq : ∀ (x : ℂ), ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := fun x => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hdouble : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      AEMeasurable (fun x => ∫⁻ k, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) (μ.restrict D) ∧
      ∫⁻ x in D, (∫⁻ k, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) ∂μ =
        (∫⁻ k, ‖κ k‖ₑ ∂μK) * ∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ := by
    intro u hu
    obtain ⟨hmeas, -, htrans⟩ := facts u hu
    have hmeasP : AEMeasurable (Function.uncurry fun (x : AdelicGL2 (𝓞 K) K) (k : ↥(adelicMaximalCompact K)) =>
        ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ) ((μ.restrict D).prod μK) :=
      (((hjoint u hmeas).norm.aemeasurable.pow_const 2).ennreal_ofReal).mul
        ((hκ.comp continuous_snd).aestronglyMeasurable.enorm)
    refine ⟨hmeasP.lintegral_prod_right', ?_⟩
    rw [lintegral_lintegral_swap hmeasP]
    calc ∫⁻ k, ∫⁻ x in D, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μ ∂μK
        = ∫⁻ k, (∫⁻ x in D, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) * ‖κ k‖ₑ ∂μK := by
          refine lintegral_congr fun k => ?_
          rw [lintegral_mul_const' _ _ enorm_ne_top, htrans (k : AdelicGL2 (𝓞 K) K)]
      _ = (∫⁻ x in D, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) * ∫⁻ k, ‖κ k‖ₑ ∂μK :=
          lintegral_const_mul'' _ hκm.enorm
      _ = _ := by rw [mul_comm, lintegral_congr fun x => hsq (u x)]

  have hL2 : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, MemLp u 2 (μ.restrict D) → ∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ < ⊤ := by
    intro u hu
    have := hu.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top] at this
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [h2] at this
    have hsq' : ∀ x : AdelicGL2 (𝓞 K) K, ‖u x‖ₑ ^ (2 : ℝ) = ‖u x‖ₑ ^ 2 := fun x => by
      rw [← ENNReal.rpow_natCast]; norm_num
    simp only [hsq'] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1 / 2)).mp this

  have hfinD : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      ∀ᵐ x ∂(μ.restrict D), ∫⁻ k, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 * ‖κ k‖ₑ ∂μK < ⊤ := by
    intro u hu
    obtain ⟨-, hL, -⟩ := facts u hu
    obtain ⟨hAE, hEq⟩ := hdouble u hu
    have h1 : ∀ᵐ x ∂(μ.restrict D), ∫⁻ k, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK < ⊤ := by
      refine ae_lt_top' hAE ?_
      change (∫⁻ x in D, (∫⁻ k, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) ∂μ) ≠ ⊤
      rw [hEq]
      exact (ENNReal.mul_lt_top hκint (hL2 u hL)).ne
    refine h1.mono fun x hx => ?_
    have heq := lintegral_congr (μ := μK) (fun k =>
      show ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ =
        ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 * ‖κ k‖ₑ by rw [hsq])
    rwa [heq] at hx

  have cs : ∀ (a b : ↥(adelicMaximalCompact K) → ℝ≥0∞), AEMeasurable a μK → AEMeasurable b μK →
      ∫⁻ k, a k * b k ∂μK ≤ (∫⁻ k, a k ^ 2 * b k ∂μK) ^ (1 / 2 : ℝ) * (∫⁻ k, b k ∂μK) ^ (1 / 2 : ℝ) := by
    intro a b ha hb
    have hhalf : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    have hhalf' : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_mul]; norm_num
    have htwo : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by
      rw [← ENNReal.rpow_natCast]; norm_num
    have h1 : ∫⁻ k, a k * b k ∂μK = ∫⁻ k, (a k * b k ^ (1 / 2 : ℝ)) * b k ^ (1 / 2 : ℝ) ∂μK :=
      lintegral_congr fun k => by rw [mul_assoc, ← pow_two, hhalf]
    have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μK Real.HolderConjugate.two_two
      (f := fun k => a k * b k ^ (1 / 2 : ℝ)) (g := fun k => b k ^ (1 / 2 : ℝ))
      (ha.mul (hb.pow_const _)) (hb.pow_const _)
    have hA : (∫⁻ k, (a k * b k ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μK) = ∫⁻ k, a k ^ 2 * b k ∂μK := by
      refine lintegral_congr fun k => ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hhalf', htwo]
    have hB : (∫⁻ k, (b k ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μK) = ∫⁻ k, b k ∂μK := lintegral_congr fun k => hhalf' _
    rw [h1]
    have h2' := h2
    simp only [Pi.mul_apply] at h2'
    rwa [hA, hB] at h2'
  have hInt : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      ∀ᵐ x ∂(μ.restrict D), Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * u (x * (k : AdelicGL2 (𝓞 K) K))) μK := by
    intro u hu
    obtain ⟨hm, -, -⟩ := facts u hu
    filter_upwards [hsect u hm, hfinD u hu] with x hxm hxf
    refine ⟨hκm.mul hxm, ?_⟩
    show ∫⁻ k, ‖κ k * u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ∂μK < ⊤
    have hle := cs (fun k => ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ) (fun k => ‖κ k‖ₑ) hxm.enorm hκm.enorm
    calc ∫⁻ k, ‖κ k * u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ∂μK
        = ∫⁻ k, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ * ‖κ k‖ₑ ∂μK := lintegral_congr fun k => by rw [enorm_mul, mul_comm]
      _ ≤ (∫⁻ k, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 * ‖κ k‖ₑ ∂μK) ^ (1 / 2 : ℝ) * (∫⁻ k, ‖κ k‖ₑ ∂μK) ^ (1 / 2 : ℝ) := hle
      _ < ⊤ := ENNReal.mul_lt_top ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hxf)
          ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hκint)
  obtain ⟨hφm, hφL2, -⟩ := facts φ hφ
  refine ⟨hInt φ hφ, ?_, ?_⟩
  ·
    filter_upwards [hInt φ hφ, hInt ψ hψ] with g h1 h2
    rw [hP, hP, hP, ← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Pi.sub_apply, mul_sub]
  ·
    have hPφ : P φ = fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK := funext (hP φ)
    rw [hPφ]

    have hpw : ∀ᵐ x ∂(μ.restrict D), ‖∫ k, κ k * φ (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK‖ₑ ^ 2 ≤
        (∫⁻ k, ENNReal.ofReal (‖φ (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) * ∫⁻ k, ‖κ k‖ₑ ∂μK := by
      filter_upwards [hsect φ hφm] with x hxm
      have := T6B.enorm_integral_mul_sq_le' μK (fun k => φ (x * (k : AdelicGL2 (𝓞 K) K))) κ hxm hκm
      rwa [show (∫ k, κ k * φ (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) = ∫ k, φ (x * (k : AdelicGL2 (𝓞 K) K)) * κ k ∂μK from
        integral_congr_ae (Filter.Eventually.of_forall fun k => mul_comm _ _)]
    obtain ⟨hAE, hEq⟩ := hdouble φ hφ
    have hcore : ∫⁻ x in D, ‖∫ k, κ k * φ (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK‖ₑ ^ 2 ∂μ ≤
        (∫⁻ k, ‖κ k‖ₑ ∂μK) ^ 2 * ∫⁻ x in D, ‖φ x‖ₑ ^ 2 ∂μ := by
      calc ∫⁻ x in D, ‖∫ k, κ k * φ (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK‖ₑ ^ 2 ∂μ
          ≤ ∫⁻ x in D, (∫⁻ k, ENNReal.ofReal (‖φ (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) *
              ∫⁻ k, ‖κ k‖ₑ ∂μK ∂μ := lintegral_mono_ae hpw
        _ = (∫⁻ x in D, (∫⁻ k, ENNReal.ofReal (‖φ (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) ∂μ) *
              ∫⁻ k, ‖κ k‖ₑ ∂μK := lintegral_mul_const'' _ hAE
        _ = ((∫⁻ k, ‖κ k‖ₑ ∂μK) * ∫⁻ x in D, ‖φ x‖ₑ ^ 2 ∂μ) * ∫⁻ k, ‖κ k‖ₑ ∂μK := by rw [hEq]
        _ = _ := by ring

    have hκI : Integrable κ μK := hκ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace κ)
    rw [ofReal_integral_norm_eq_lintegral_enorm hκI,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [h2]
    have hsq2 : ∀ (x : ℂ), ‖x‖ₑ ^ (2 : ℝ) = ‖x‖ₑ ^ 2 := fun x => by
      rw [← ENNReal.rpow_natCast]; norm_num
    simp only [hsq2]
    have hhalf2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    calc (∫⁻ x in D, ‖∫ k, κ k * φ (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        ≤ ((∫⁻ k, ‖κ k‖ₑ ∂μK) ^ 2 * ∫⁻ x in D, ‖φ x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hcore (by norm_num)
      _ = (∫⁻ k, ‖κ k‖ₑ ∂μK) * (∫⁻ x in D, ‖φ x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hhalf2]

end Ws35H.PD

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
    ∀ (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ) (_hψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ),
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * φ (g * (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), P (φ - ψ) g = P φ g - P ψ g) ∧
    eLpNorm (P φ) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ ENNReal.ofReal (∫ k, ‖κ k‖ ∂(maximalCompactHaar K)) * eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
  Ws35H.PD.pd_main K α β hα hαβ ξK hξc hξt hξu

end S_AutomorphicForm_ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
end P2MW
export P2MW.S_AutomorphicForm_ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact (solution)
