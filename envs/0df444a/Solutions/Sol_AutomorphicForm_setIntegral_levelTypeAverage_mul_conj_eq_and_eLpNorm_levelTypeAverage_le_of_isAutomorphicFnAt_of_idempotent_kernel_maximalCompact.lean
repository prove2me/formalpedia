-- Prove2me | solution 1 for AutomorphicForm.setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/63278135-8e18-5226-a20b-9381da340801

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
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
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
      K α β Φ hΦs hΦ h hh (fun x => ((min (‖u x‖ ^ 2) (n : ℝ) : ℝ) : ℂ)) (fun γ g => by rw [hΓ γ g])
    try dsimp only at hB
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

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (κ : ↥(adelicMaximalCompact K) → ℂ) (hκ : Continuous κ) (hκs : ∀ k, κ k⁻¹ = conj (κ k))
    (hκi : ∀ k : ↥(adelicMaximalCompact K), ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k) :
    ∀ φ ψ : AdelicGL2 (𝓞 K) K → ℂ,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ →
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun g => (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) ∧
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) * conj (ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            φ g * conj (∫ k, κ k * ψ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ∧
        eLpNorm (fun g => (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  intro φ ψ hφ hψ
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
  have hKc : IsCompact (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := isCompact_adelicMaximalCompact K
  have hdet : ∀ k : ↥(adelicMaximalCompact K),
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) = 1 :=
    fun k => NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem K (adelicMaximalCompact K) hKc _ k.2
  have hsq : ∀ (x : ℂ), ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := fun x => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have h2r : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hsq2 : ∀ (x : ℂ), ‖x‖ₑ ^ (2 : ℝ) = ‖x‖ₑ ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hhalf2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have heLp : ∀ (ν : Measure (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ),
      eLpNorm u 2 ν = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    intro ν u
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [h2r, hsq2]

  have facts : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      IsLsXiFunction (𝓞 K) K ⊤ ξK u ∧ AEStronglyMeasurable u μ ∧ MemLp u 2 (μ.restrict D) ∧
      ∀ k : ↥(adelicMaximalCompact K), ∫⁻ x in D, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) ∂μ =
        ∫⁻ x in D, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
    intro u hu
    have hLs : IsLsXiFunction (𝓞 K) K ⊤ ξK u ∧ MemLp u 2 (μ.restrict D) :=
      (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
    have hΓ := hLs.1.left_invariant
    have hmeas : AEStronglyMeasurable u μ :=
      AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ D hslab hFD ξK u hu
    refine ⟨hLs.1, hmeas, hLs.2, fun k => ?_⟩
    exact T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq K α β _ hslab hFD hfin u hmeas hΓ _ (hdet k)

  have hL2 : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, MemLp u 2 (μ.restrict D) → ∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ < ⊤ := by
    intro u hu
    have := hu.eLpNorm_lt_top
    rw [heLp] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1 / 2)).mp this

  have hκm : AEStronglyMeasurable κ μK := hκ.aestronglyMeasurable
  have hκI : Integrable κ μK := hκ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace κ)
  have hκint : ∫⁻ k, ‖κ k‖ₑ ∂μK < ⊤ := hκI.2

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

  have hdouble : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      AEMeasurable (fun x => ∫⁻ k, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) (μ.restrict D) ∧
      ∫⁻ x in D, (∫⁻ k, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μK) ∂μ =
        (∫⁻ k, ‖κ k‖ₑ ∂μK) * ∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ := by
    intro u hu
    obtain ⟨-, hmeas, -, htrans⟩ := facts u hu
    have hmeasP : AEMeasurable (Function.uncurry fun (x : AdelicGL2 (𝓞 K) K) (k : ↥(adelicMaximalCompact K)) =>
        ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ) ((μ.restrict D).prod μK) :=
      (((hjoint u hmeas).norm.aemeasurable.pow_const 2).ennreal_ofReal).mul
        ((hκ.comp continuous_snd).aestronglyMeasurable.enorm)
    refine ⟨hmeasP.lintegral_prod_right', ?_⟩
    rw [lintegral_lintegral_swap hmeasP]
    calc ∫⁻ k, ∫⁻ x in D, ENNReal.ofReal (‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) * ‖κ k‖ₑ ∂μ ∂μK
        = ∫⁻ k, (∫⁻ x in D, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) * ‖κ k‖ₑ ∂μK := by
          refine lintegral_congr fun k => ?_
          rw [lintegral_mul_const' _ _ enorm_ne_top, htrans k]
      _ = (∫⁻ x in D, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) * ∫⁻ k, ‖κ k‖ₑ ∂μK :=
          lintegral_const_mul'' _ hκm.enorm
      _ = _ := by rw [mul_comm, lintegral_congr fun x => hsq (u x)]

  have hfinD : ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      ∀ᵐ x ∂(μ.restrict D), ∫⁻ k, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 * ‖κ k‖ₑ ∂μK < ⊤ := by
    intro u hu
    obtain ⟨-, -, hL, -⟩ := facts u hu
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
    obtain ⟨-, hm, -, -⟩ := facts u hu
    filter_upwards [hsect u hm, hfinD u hu] with x hxm hxf
    refine ⟨hκm.mul hxm, ?_⟩
    show ∫⁻ k, ‖κ k * u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ∂μK < ⊤
    have hle := cs (fun k => ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ) (fun k => ‖κ k‖ₑ) hxm.enorm hκm.enorm
    calc ∫⁻ k, ‖κ k * u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ∂μK
        = ∫⁻ k, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ * ‖κ k‖ₑ ∂μK := lintegral_congr fun k => by rw [enorm_mul, mul_comm]
      _ ≤ (∫⁻ k, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 * ‖κ k‖ₑ ∂μK) ^ (1 / 2 : ℝ) * (∫⁻ k, ‖κ k‖ₑ ∂μK) ^ (1 / 2 : ℝ) := hle
      _ < ⊤ := ENNReal.mul_lt_top ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hxf)
          ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hκint)
  obtain ⟨hφLs, hφm, hφL2, hφtr⟩ := facts φ hφ
  obtain ⟨hφLs, hφm, hφL2, hφtr⟩ := facts φ hφ
  obtain ⟨hψLs, hψm, hψL2, hψtr⟩ := facts ψ hψ

  have hAVR := fun (u v : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v) =>
    AutomorphicForm.isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
      K α β hα hαβ ξK κ hκ u v hu hv
  obtain ⟨-, -, -, hPφaut, hPφbd⟩ := hAVR φ ψ hφ hψ

  haveI hKR : μK.IsMulRightInvariant := by
    constructor
    intro g
    have hμ' := MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace (μK.map (· * g)) μK
    have h1 : (μK.map (· * g)) Set.univ = 1 := by
      rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ, measure_univ]
    have hc : MeasureTheory.Measure.haarScalarFactor (μK.map (· * g)) μK = 1 := by
      have h2 := congrArg (fun ν : Measure (adelicMaximalCompact K) => ν Set.univ) hμ'
      simp only [h1, Measure.smul_apply, measure_univ] at h2
      have h4 := h2.symm
      rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h4
      exact ENNReal.coe_eq_one.1 h4
    rw [hc, one_smul] at hμ'
    exact hμ'
  haveI hKI : μK.IsInvInvariant := by
    constructor
    have hμ' := MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace μK.inv μK
    have h1 : μK.inv Set.univ = 1 := by
      rw [Measure.inv_apply, Set.inv_univ, measure_univ]
    have hc : MeasureTheory.Measure.haarScalarFactor μK.inv μK = 1 := by
      have h2 := congrArg (fun ν : Measure (adelicMaximalCompact K) => ν Set.univ) hμ'
      simp only [h1, Measure.smul_apply, measure_univ] at h2
      have h4 := h2.symm
      rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h4
      exact ENNReal.coe_eq_one.1 h4
    rw [hc, one_smul] at hμ'
    exact hμ'

  have hadj : ∀ (u v : AdelicGL2 (𝓞 K) K → ℂ), IsLsXiFunction (𝓞 K) K ⊤ ξK u → IsLsXiFunction (𝓞 K) K ⊤ ξK v →
      ∀ k : ↥(adelicMaximalCompact K),
      ∫ x in D, u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x) ∂μ = ∫ x in D, u x * conj (v (x * (k : AdelicGL2 (𝓞 K) K)⁻¹)) ∂μ := by
    intro u v hu hv k
    have h := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
      K α β D hslab hFD (k : AdelicGL2 (𝓞 K) K) (hdet k) (fun x => u x * conj (v (x * (k : AdelicGL2 (𝓞 K) K)⁻¹))) (fun γ g => by
        show u (globalPoints (𝓞 K) K γ * g) * conj (v (globalPoints (𝓞 K) K γ * g * (k : AdelicGL2 (𝓞 K) K)⁻¹)) =
          u g * conj (v (g * (k : AdelicGL2 (𝓞 K) K)⁻¹))
        rw [hu.left_invariant, mul_assoc, hv.left_invariant])
    simpa only [mul_inv_cancel_right] using h

  have hmeasR : ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable u μ → ∀ k : ↥(adelicMaximalCompact K),
      AEStronglyMeasurable (fun x => u (x * (k : AdelicGL2 (𝓞 K) K))) (μ.restrict D) := fun u hu k =>
    (hu.comp_quasiMeasurePreserving (measurePreserving_mul_right μ (k : AdelicGL2 (𝓞 K) K)).quasiMeasurePreserving).restrict
  have hpair : ∀ (u v : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
      Integrable (fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) =>
        κ p.2 * u (p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) * conj (v p.1)) ((μ.restrict D).prod μK) := by
    intro u v hu hv
    obtain ⟨-, hum, huL, hutr⟩ := facts u hu
    obtain ⟨-, hvm, hvL, -⟩ := facts v hv
    have hmeas : AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) =>
        κ p.2 * u (p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) * conj (v p.1)) ((μ.restrict D).prod μK) :=
      (((hκ.comp continuous_snd).aestronglyMeasurable).mul (hjoint u hum)).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable hvm.restrict.comp_fst)
    refine ⟨hmeas, ?_⟩
    show ∫⁻ p, ‖κ p.2 * u (p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) * conj (v p.1)‖ₑ ∂((μ.restrict D).prod μK) < ⊤
    have hmE : AEMeasurable (fun p : AdelicGL2 (𝓞 K) K × ↥(adelicMaximalCompact K) =>
        ‖κ p.2 * u (p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) * conj (v p.1)‖ₑ) ((μ.restrict D).prod μK) := hmeas.enorm
    rw [lintegral_prod_symm _ hmE]
    have hB := hL2 v hvL
    have hA := hL2 u huL
    calc ∫⁻ k, ∫⁻ x, ‖κ k * u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x)‖ₑ ∂(μ.restrict D) ∂μK
        = ∫⁻ k, ‖κ k‖ₑ * ∫⁻ x, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ * ‖v x‖ₑ ∂(μ.restrict D) ∂μK := by
          refine lintegral_congr fun k => ?_
          rw [← lintegral_const_mul'' _ (((hmeasR u hum k).enorm).fun_mul hvm.restrict.enorm)]
          refine lintegral_congr fun x => ?_
          rw [enorm_mul, enorm_mul, RCLike.enorm_conj, mul_assoc]
      _ ≤ ∫⁻ k, ‖κ k‖ₑ * ((∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x in D, ‖v x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ∂μK := by
          refine lintegral_mono fun k => mul_le_mul_right ?_ _
          have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict D) Real.HolderConjugate.two_two
            ((hmeasR u hum k).enorm) hvm.restrict.enorm
          have hsq2' : ∀ (w : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K), ‖w x‖ₑ ^ (2 : ℝ) = ‖w x‖ₑ ^ 2 := fun w x => hsq2 (w x)
          simp only [Pi.mul_apply, hsq2'] at hH
          have htr : ∫⁻ x in D, ‖u (x * (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 ∂μ = ∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ := by
            have := hutr k
            simpa only [hsq] using this
          rw [htr] at hH
          exact hH
      _ = (∫⁻ k, ‖κ k‖ₑ ∂μK) * ((∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x in D, ‖v x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) :=
          lintegral_mul_const'' _ hκm.enorm
      _ < ⊤ := ENNReal.mul_lt_top hκint (ENNReal.mul_lt_top
          ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hA) ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hB))
  have hSA : ∀ (u v : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v),
      ∫ x in D, (∫ k, κ k * u (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) * conj (v x) ∂μ =
        ∫ x in D, u x * conj (∫ k, κ k * v (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) ∂μ := by
    intro u v hu hv
    obtain ⟨huLs, hum, huL2, hutr⟩ := facts u hu
    obtain ⟨hvLs, hvm, hvL2, hvtr⟩ := facts v hv
    have hI := hpair u v hu hv
    have hJ := hpair v u hv hu

    have hL : ∫ x in D, (∫ k, κ k * u (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) * conj (v x) ∂μ =
        ∫ k, κ k * ∫ x in D, u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x) ∂μ ∂μK := by
      calc ∫ x in D, (∫ k, κ k * u (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) * conj (v x) ∂μ
          = ∫ x in D, ∫ k, κ k * u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x) ∂μK ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            exact (integral_mul_const _ _).symm
        _ = ∫ k, ∫ x in D, κ k * u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x) ∂μ ∂μK :=
            integral_integral_swap hI
        _ = ∫ k, κ k * ∫ x in D, u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x) ∂μ ∂μK := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
            dsimp only
            rw [← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            ring

    have hR : ∫ x in D, u x * conj (∫ k, κ k * v (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) ∂μ =
        ∫ k, conj (κ k) * ∫ x in D, u x * conj (v (x * (k : AdelicGL2 (𝓞 K) K))) ∂μ ∂μK := by
      calc ∫ x in D, u x * conj (∫ k, κ k * v (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) ∂μ
          = ∫ x in D, ∫ k, conj (κ k * v (x * (k : AdelicGL2 (𝓞 K) K)) * conj (u x)) ∂μK ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            dsimp only
            rw [← integral_conj, ← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
            simp only [map_mul, Complex.conj_conj]
            ring
        _ = ∫ k, ∫ x in D, conj (κ k * v (x * (k : AdelicGL2 (𝓞 K) K)) * conj (u x)) ∂μ ∂μK := by
            refine integral_integral_swap ?_
            refine hJ.congr' (Complex.continuous_conj.comp_aestronglyMeasurable hJ.1) ?_
            exact Filter.Eventually.of_forall fun p => by
              rcases p with ⟨x, k⟩
              simp only [Function.uncurry_apply_pair, norm_mul, RCLike.norm_conj]
        _ = ∫ k, conj (κ k) * ∫ x in D, u x * conj (v (x * (k : AdelicGL2 (𝓞 K) K))) ∂μ ∂μK := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
            dsimp only
            rw [← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [map_mul, Complex.conj_conj]
            ring
    rw [hL, hR]

    have hS := integral_inv_eq_self (fun k : ↥(adelicMaximalCompact K) =>
      conj (κ k) * ∫ x in D, u x * conj (v (x * (k : AdelicGL2 (𝓞 K) K))) ∂μ) μK
    rw [← hS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show κ k * ∫ x in D, u (x * (k : AdelicGL2 (𝓞 K) K)) * conj (v x) ∂μ =
      conj (κ k⁻¹) * ∫ x in D, u x * conj (v (x * ((k⁻¹ : ↥(adelicMaximalCompact K)) : AdelicGL2 (𝓞 K) K))) ∂μ
    rw [hκs, Complex.conj_conj, hadj u v huLs hvLs k, Subgroup.coe_inv]
  refine ⟨hPφaut, hSA φ ψ hφ hψ, ?_⟩

  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK with hFdef
  obtain ⟨hFLs, hFm, hFL2, hFtr⟩ := facts F hPφaut

  obtain ⟨-, hφK1, -, -, -⟩ :=
    AutomorphicForm.isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
      K α β hα hαβ ξK (fun _ => (1 : ℂ)) continuous_const φ φ hφ hφ
  obtain ⟨Cκ, hCκ⟩ := isCompact_univ.exists_bound_of_continuousOn (hκ.continuousOn (s := Set.univ))
  have hCκ' : ∀ k : ↥(adelicMaximalCompact K), ‖κ k‖ ≤ Cκ := fun k => hCκ k (Set.mem_univ k)
  have hC0 : 0 ≤ Cκ := (norm_nonneg _).trans (hCκ' 1)

  have hidem : ∀ᵐ x ∂(μ.restrict D), (∫ k, κ k * F (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK) = F x := by
    filter_upwards [hφK1, hsect φ hφm] with x hx1 hxm
    have hφx : Integrable (fun m : ↥(adelicMaximalCompact K) => φ (x * (m : AdelicGL2 (𝓞 K) K))) μK := by
      simpa only [one_mul] using hx1
    haveI : SecondCountableTopology ↥(adelicMaximalCompact K) := TopologicalSpace.Subtype.secondCountableTopology _
    have hmeasG : AEStronglyMeasurable (fun z : ↥(adelicMaximalCompact K) × ↥(adelicMaximalCompact K) =>
        κ z.1 * (κ (z.1⁻¹ * z.2) * φ (x * (z.2 : AdelicGL2 (𝓞 K) K)))) (μK.prod μK) :=
      ((hκ.comp continuous_fst).aestronglyMeasurable).mul
        (((hκ.comp (continuous_fst.inv.mul continuous_snd)).aestronglyMeasurable).mul hxm.comp_snd)
    have hG : Integrable (fun z : ↥(adelicMaximalCompact K) × ↥(adelicMaximalCompact K) =>
        κ z.1 * (κ (z.1⁻¹ * z.2) * φ (x * (z.2 : AdelicGL2 (𝓞 K) K)))) (μK.prod μK) := by
      refine Integrable.mono' ((integrable_const (Cκ * Cκ)).mul_prod hφx.norm) hmeasG
        (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul, norm_mul, ← mul_assoc]
      exact mul_le_mul (mul_le_mul (hCκ' _) (hCκ' _) (norm_nonneg _) hC0) le_rfl (norm_nonneg _)
        (mul_nonneg hC0 hC0)
    calc (∫ k, κ k * F (x * (k : AdelicGL2 (𝓞 K) K)) ∂μK)
        = ∫ k, ∫ k', κ k * (κ k' * φ (x * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K))) ∂μK ∂μK := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          show κ k * (∫ k', κ k' * φ (x * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂μK) = _
          rw [← integral_const_mul]
      _ = ∫ k, ∫ m, κ k * (κ (k⁻¹ * m) * φ (x * (m : AdelicGL2 (𝓞 K) K))) ∂μK ∂μK := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          dsimp only
          rw [← integral_mul_left_eq_self (fun m : ↥(adelicMaximalCompact K) => κ k * (κ (k⁻¹ * m) * φ (x * (m : AdelicGL2 (𝓞 K) K)))) k]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k' => ?_)
          dsimp only
          rw [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]
      _ = ∫ m, ∫ k, κ k * (κ (k⁻¹ * m) * φ (x * (m : AdelicGL2 (𝓞 K) K))) ∂μK ∂μK := integral_integral_swap hG
      _ = ∫ m, (∫ k, κ k * κ (k⁻¹ * m) ∂μK) * φ (x * (m : AdelicGL2 (𝓞 K) K)) ∂μK := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
          dsimp only
          rw [← integral_mul_const]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          ring
      _ = ∫ m, κ m * φ (x * (m : AdelicGL2 (𝓞 K) K)) ∂μK := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
          dsimp only
          rw [hκi m]
      _ = F x := rfl

  have hkey : ∫ x in D, F x * conj (F x) ∂μ = ∫ x in D, φ x * conj (F x) ∂μ := by
    have h1 := hSA φ F hφ hPφaut
    refine h1.trans ?_
    refine integral_congr_ae ?_
    filter_upwards [hidem] with x hx
    rw [hx]

  have hint2F : Integrable (fun x => ‖F x‖ ^ 2) (μ.restrict D) := (memLp_two_iff_integrable_sq_norm hFL2.1).1 hFL2
  have hint2φ : Integrable (fun x => ‖φ x‖ ^ 2) (μ.restrict D) := (memLp_two_iff_integrable_sq_norm hφL2.1).1 hφL2
  set a : ℝ := ∫ x in D, ‖F x‖ ^ 2 ∂μ with ha
  set b : ℝ := ∫ x in D, ‖φ x‖ ^ 2 ∂μ with hb
  have ha0 : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun _ => sq_nonneg _
  have hFF : ∫ x in D, F x * conj (F x) ∂μ = ((a : ℝ) : ℂ) := by
    rw [ha, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * conj (F x) = ((‖F x‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hholder : ∫ x in D, ‖φ x‖ * ‖F x‖ ∂μ ≤ Real.sqrt b * Real.sqrt a := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict D) Real.HolderConjugate.two_two
      (f := fun x => ‖φ x‖) (g := fun x => ‖F x‖)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (by rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hφL2.norm)
      (by rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hFL2.norm)
    simp_rw [Real.rpow_two] at h
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, hb, ha]
    exact h
  have hle : a ≤ Real.sqrt b * Real.sqrt a := by
    calc a = Complex.re (∫ x in D, φ x * conj (F x) ∂μ) := by rw [← hkey, hFF, Complex.ofReal_re]
      _ ≤ ‖∫ x in D, φ x * conj (F x) ∂μ‖ := Complex.re_le_norm _
      _ ≤ ∫ x in D, ‖φ x * conj (F x)‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x in D, ‖φ x‖ * ‖F x‖ ∂μ := by simp only [norm_mul, RCLike.norm_conj]
      _ ≤ Real.sqrt b * Real.sqrt a := hholder
  have hab : a ≤ b := by
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · rw [← h0]; exact hb0
    · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 hpos
      have h3 : Real.sqrt a ≤ Real.sqrt b := by
        have h4 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt b * Real.sqrt a := by rwa [Real.mul_self_sqrt ha0]
        exact le_of_mul_le_mul_right h4 hsa
      calc a = (Real.sqrt a) ^ 2 := (Real.sq_sqrt ha0).symm
        _ ≤ (Real.sqrt b) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
        _ = b := Real.sq_sqrt hb0

  rw [heLp, heLp]
  have hlin : ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), Integrable (fun x => ‖u x‖ ^ 2) (μ.restrict D) →
      ∫⁻ x in D, ‖u x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x in D, ‖u x‖ ^ 2 ∂μ) := by
    intro u hu
    rw [ofReal_integral_eq_lintegral_ofReal hu (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact lintegral_congr fun x => (hsq (u x)).symm
  rw [hlin F hint2F, hlin φ hint2φ]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hab) (by norm_num)

end S_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact (solution)
