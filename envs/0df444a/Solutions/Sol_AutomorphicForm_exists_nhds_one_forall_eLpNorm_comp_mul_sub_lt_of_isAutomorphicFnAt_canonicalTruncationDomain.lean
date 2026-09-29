-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/199252c6-38ee-53bd-8608-f4c62c2ef514

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
import Theorems.Thm_MeasureTheory_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped Pointwise ENNReal Topology
open AutomorphicForm

noncomputable section

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

namespace V1B

variable (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem facts (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) :
    AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
    ∀ y : AdelicGL2 (𝓞 K) K,
      ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ‖u (x * y)‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ‖u x‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set D := AutomorphicForm.canonicalTruncationDomain K α β with hD
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : μ D < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ D hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  have hLs : IsLsXiFunction (𝓞 K) K ⊤ ξK u ∧ MemLp u 2 (μ.restrict D) := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
  have hΓ := hLs.1.left_invariant
  have hZ := hLs.1.central_transform
  have hmeas : AEStronglyMeasurable u μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ D hslab hFD ξK u hu
  have hsq : ∀ (x : ℂ), ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := fun x => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
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
  have key := T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq K α β _ hslab hFD hfin u hmeas hΓ _ hh
  simp only [hsq] at key
  rw [← key]
  exact lintegral_congr fun x => by rw [← hsq, ← hsq, hpt]

end V1B

end

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (v : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : AdelicGL2 (𝓞 K) K), ∀ x ∈ U,
      eLpNorm (fun g : AdelicGL2 (𝓞 K) K => v (g * x) - v g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set D := AutomorphicForm.canonicalTruncationDomain K α β with hD
  obtain ⟨hmeas, hL2, hiso⟩ := V1B.facts K α β hα hαβ ξK hξu v _hv
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : μ D < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ D hFD
    rwa [Set.inter_eq_left.mpr hslab] at h

  set S : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hS
  have hslabm : MeasurableSet S := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  have hDnull : NullMeasurableSet D μ := by
    obtain ⟨t, ht_sub, htm, hteq⟩ := hFD.nullMeasurableSet.exists_measurable_superset_ae_eq
    have h1 : (μ.restrict S) (t \ D) = 0 := ae_le_set.mp hteq.le
    rw [Measure.restrict_apply' hslabm] at h1
    have hae : (t ∩ S : Set (AdelicGL2 (𝓞 K) K)) =ᵐ[μ] D := by
      refine (ae_eq_set).mpr ⟨?_, ?_⟩
      · have e : (t ∩ S) \ D = (t \ D) ∩ S := by
          ext g; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
        rw [e]; exact h1
      · have e : D \ (t ∩ S) = ∅ := Set.diff_eq_empty.mpr fun g hg => ⟨ht_sub hg, hslab hg⟩
        rw [e, measure_empty]
    exact (htm.inter hslabm).nullMeasurableSet.congr hae
  obtain ⟨D', hD'sup, hD'm, hD'ae⟩ := hDnull.exists_measurable_superset_ae_eq
  have hres : μ.restrict D' = μ.restrict D := Measure.restrict_congr_set hD'ae
  have hfin' : μ D' < ⊤ := by rw [measure_congr hD'ae]; exact hfin

  set f₀ : AdelicGL2 (𝓞 K) K → ℝ≥0∞ := fun g => ‖v g‖ₑ ^ 2 with hf₀
  have hf₀D : ∫⁻ g in D', f₀ g ∂μ < ⊤ := by
    rw [show (∫⁻ g in D', f₀ g ∂μ) = ∫⁻ g in D, f₀ g ∂μ from by rw [hres]]
    have := hL2.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top] at this
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [h2] at this
    have hsq' : ∀ x : AdelicGL2 (𝓞 K) K, ‖v x‖ₑ ^ (2 : ℝ) = ‖v x‖ₑ ^ 2 := fun x => by
      rw [← ENNReal.rpow_natCast]; norm_num
    simp only [hsq'] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1 / 2)).mp this

  have heLp : ∀ (ν : Measure (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ),
      eLpNorm u 2 ν = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    intro ν u
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    have h2r : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have hsq2 : ∀ (x : ℂ), ‖x‖ₑ ^ (2 : ℝ) = ‖x‖ₑ ^ 2 := fun x => by rw [← ENNReal.rpow_natCast]; norm_num
    simp only [h2r, hsq2]
  have hhalf2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hhalf' : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

  set F : AdelicGL2 (𝓞 K) K → ℂ := D'.indicator v with hF
  set χ : AdelicGL2 (𝓞 K) K → ℂ := D'.indicator (fun _ => (1 : ℂ)) with hχ
  have hFmem : MemLp F 2 μ := (memLp_indicator_iff_restrict hD'm).2 (by rw [hres]; exact hL2)
  have hχmem : MemLp χ 2 μ := memLp_indicator_const 2 hD'm (1 : ℂ) (Or.inr hfin'.ne)

  have hε4 : 0 < ε / 4 := by linarith
  set η : ℝ≥0∞ := (ENNReal.ofReal (ε / 4)) ^ 2 with hη
  have hη0 : η ≠ 0 := by
    rw [hη]; exact pow_ne_zero 2 (by rw [ENNReal.ofReal_ne_zero_iff]; exact hε4)
  have hf₀int : ∫⁻ g, D'.indicator f₀ g ∂μ ≠ ⊤ := by
    rw [lintegral_indicator hD'm]; exact hf₀D.ne
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf₀int hη0

  have hδr : 0 < (min δ 1).toReal := ENNReal.toReal_pos (lt_min hδ0 one_pos).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  set ε₂ : ℝ := Real.sqrt ((min δ 1).toReal) / 2 with hε₂
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; exact div_pos (Real.sqrt_pos.2 hδr) two_pos
  have hε₂δ : (ENNReal.ofReal ε₂) ^ 2 < δ := by
    have h1 : (ENNReal.ofReal ε₂) ^ 2 = ENNReal.ofReal ((min δ 1).toReal / 4) := by
      rw [← ENNReal.ofReal_pow hε₂0.le, hε₂, div_pow, Real.sq_sqrt hδr.le]; norm_num
    rw [h1]
    calc ENNReal.ofReal ((min δ 1).toReal / 4) < ENNReal.ofReal ((min δ 1).toReal) := by
          rw [ENNReal.ofReal_lt_ofReal_iff hδr]; linarith
      _ = min δ 1 := ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
      _ ≤ δ := min_le_left _ _

  obtain ⟨V₂, hV₂, hB⟩ := MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two μ F hFmem (ε / 4) hε4
  obtain ⟨V₁, hV₁, hχc⟩ := MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two μ χ hχmem ε₂ hε₂0
  have hV₁' : (fun x : AdelicGL2 (𝓞 K) K => x⁻¹) ⁻¹' V₁ ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K) := by
    refine continuous_inv.continuousAt.preimage_mem_nhds ?_
    simpa using hV₁
  refine ⟨V₂ ∩ (fun x : AdelicGL2 (𝓞 K) K => x⁻¹) ⁻¹' V₁, Filter.inter_mem hV₂ hV₁', fun x hx => ?_⟩
  obtain ⟨hx₂, hx₁⟩ := hx
  have hx₁' : x⁻¹ ∈ V₁ := hx₁

  set Sx : Set (AdelicGL2 (𝓞 K) K) := (fun g => g * x) ⁻¹' D' with hSx
  set P : Set (AdelicGL2 (𝓞 K) K) := (fun g => g * x⁻¹) ⁻¹' D' with hP
  have hSxm : MeasurableSet Sx := hD'm.preimage (measurable_id.mul_const x)
  have hPm : MeasurableSet P := hD'm.preimage (measurable_id.mul_const x⁻¹)
  have hEmb : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 K) K => g * x) := (MeasurableEquiv.mulRight x).measurableEmbedding

  have him1 : (fun g => g * x) '' (D' \ Sx) = P \ D' := by
    rw [Set.image_mul_right]; ext g
    simp only [Set.mem_preimage, Set.mem_diff, hSx, hP, inv_mul_cancel_right]
  have him2 : (fun g => g * x) '' (Sx \ D') = D' \ P := by
    rw [Set.image_mul_right]; ext g
    simp only [Set.mem_preimage, Set.mem_diff, hSx, hP, inv_mul_cancel_right]
  have him3 : (fun g => g * x) '' D' = P := by
    rw [Set.image_mul_right]

  have hsmall : μ (D' \ P) < δ := by

    have hpt : ∀ g, (D' \ P).indicator (fun _ => (1 : ℝ≥0∞)) g ≤ ‖χ (g * x⁻¹) - χ g‖ₑ ^ 2 := by
      intro g
      by_cases hg : g ∈ D' \ P
      · rw [Set.indicator_of_mem hg]
        have h1 : χ g = 1 := Set.indicator_of_mem hg.1 _
        have h2 : χ (g * x⁻¹) = 0 := by
          show D'.indicator (fun _ => (1 : ℂ)) (g * x⁻¹) = 0
          exact Set.indicator_of_notMem (fun h : g * x⁻¹ ∈ D' => hg.2 h) _
        rw [h1, h2]; simp
      · rw [Set.indicator_of_notMem hg]; exact zero_le
    have hle : μ (D' \ P) ≤ ∫⁻ g, ‖χ (g * x⁻¹) - χ g‖ₑ ^ 2 ∂μ := by
      rw [← lintegral_indicator_one (hD'm.diff hPm)]
      exact lintegral_mono hpt
    have hlt : (∫⁻ g, ‖χ (g * x⁻¹) - χ g‖ₑ ^ 2 ∂μ) < (ENNReal.ofReal ε₂) ^ 2 := by
      have h := hχc x⁻¹ hx₁'
      rw [heLp] at h
      have := ENNReal.rpow_lt_rpow h (show (0:ℝ) < 2 by norm_num)
      rw [← ENNReal.rpow_mul] at this
      norm_num at this
      rw [← ENNReal.rpow_natCast]
      simpa using this
    exact (hle.trans_lt hlt).trans hε₂δ
  have hb : ∫⁻ g in D' \ P, f₀ g ∂μ < η := by
    have h1 := hδ (D' \ P) hsmall
    have h2 : ∫⁻ g in D' \ P, D'.indicator f₀ g ∂μ = ∫⁻ g in D' \ P, f₀ g ∂μ :=
      setLIntegral_congr_fun (hD'm.diff hPm) (fun g hg => Set.indicator_of_mem hg.1 _)
    rwa [h2] at h1

  have hA1 : ∫⁻ g in D' \ Sx, f₀ (g * x) ∂μ = ∫⁻ g in P \ D', f₀ g ∂μ := by
    rw [(measurePreserving_mul_right μ x).setLIntegral_comp_emb hEmb f₀ (D' \ Sx), him1]
  have hC1 : ∫⁻ g in Sx \ D', f₀ (g * x) ∂μ = ∫⁻ g in D' \ P, f₀ g ∂μ := by
    rw [(measurePreserving_mul_right μ x).setLIntegral_comp_emb hEmb f₀ (Sx \ D'), him2]
  have hP1 : ∫⁻ g in P, f₀ g ∂μ = ∫⁻ g in D', f₀ g ∂μ := by
    rw [← him3, ← (measurePreserving_mul_right μ x).setLIntegral_comp_emb hEmb f₀ D',
      setLIntegral_congr hD'ae, setLIntegral_congr hD'ae]
    exact hiso x
  have hcancel : ∫⁻ g in P \ D', f₀ g ∂μ = ∫⁻ g in D' \ P, f₀ g ∂μ := by
    have e1 := lintegral_inter_add_diff (μ := μ) f₀ P hD'm
    have e2 := lintegral_inter_add_diff (μ := μ) f₀ D' hPm
    rw [Set.inter_comm] at e2
    have hc : ∫⁻ g in P ∩ D', f₀ g ∂μ ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono_set Set.inter_subset_right) hf₀D).ne
    have h : ∫⁻ g in P ∩ D', f₀ g ∂μ + ∫⁻ g in P \ D', f₀ g ∂μ =
        ∫⁻ g in P ∩ D', f₀ g ∂μ + ∫⁻ g in D' \ P, f₀ g ∂μ := by rw [e1, hP1, e2]
    exact (ENNReal.add_right_inj hc).1 h

  have hvx : AEStronglyMeasurable (fun g => v (g * x)) μ :=
    hmeas.comp_quasiMeasurePreserving (measurePreserving_mul_right μ x).quasiMeasurePreserving
  have hFm : AEStronglyMeasurable F μ := hmeas.indicator hD'm
  have hFx : AEStronglyMeasurable (fun g => F (g * x)) μ :=
    hFm.comp_quasiMeasurePreserving (measurePreserving_mul_right μ x).quasiMeasurePreserving
  set A : AdelicGL2 (𝓞 K) K → ℂ := (D' \ Sx).indicator (fun g => v (g * x)) with hAdef
  set Bf : AdelicGL2 (𝓞 K) K → ℂ := fun g => F (g * x) - F g with hBdef
  set C : AdelicGL2 (𝓞 K) K → ℂ := (Sx \ D').indicator (fun g => v (g * x)) with hCdef
  have hAm : AEStronglyMeasurable A μ := hvx.indicator (hD'm.diff hSxm)
  have hBm : AEStronglyMeasurable Bf μ := hFx.sub hFm
  have hCm : AEStronglyMeasurable C μ := hvx.indicator (hSxm.diff hD'm)
  have hdecomp : D'.indicator (fun g => v (g * x) - v g) = A + (Bf - C) := by
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, hAdef, hBdef, hCdef, hF]
    by_cases hg : g ∈ D'
    · by_cases hgx : g * x ∈ D'
      · have h1 : g ∉ D' \ Sx := fun h => h.2 hgx
        have h2 : g ∉ Sx \ D' := fun h => h.2 hg
        rw [Set.indicator_of_mem hg, Set.indicator_of_notMem h1, Set.indicator_of_mem hgx,
          Set.indicator_of_mem hg, Set.indicator_of_notMem h2]; ring
      · have h1 : g ∈ D' \ Sx := ⟨hg, hgx⟩
        have h2 : g ∉ Sx \ D' := fun h => h.2 hg
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem h1, Set.indicator_of_notMem hgx,
          Set.indicator_of_mem hg, Set.indicator_of_notMem h2]; ring
    · by_cases hgx : g * x ∈ D'
      · have h1 : g ∉ D' \ Sx := fun h => hg h.1
        have h2 : g ∈ Sx \ D' := ⟨hgx, hg⟩
        rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h1, Set.indicator_of_mem hgx,
          Set.indicator_of_notMem hg, Set.indicator_of_mem h2]; ring
      · have h1 : g ∉ D' \ Sx := fun h => hg h.1
        have h2 : g ∉ Sx \ D' := fun h => h.1 |> fun h' => hgx h'
        rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h1, Set.indicator_of_notMem hgx,
          Set.indicator_of_notMem hg, Set.indicator_of_notMem h2]; ring
  have hηhalf : η ^ (1 / 2 : ℝ) = ENNReal.ofReal (ε / 4) := by rw [hη, hhalf2]
  have hAlt : eLpNorm A 2 μ < ENNReal.ofReal (ε / 4) := by
    rw [hAdef, eLpNorm_indicator_eq_eLpNorm_restrict (hD'm.diff hSxm), heLp]
    show (∫⁻ g in D' \ Sx, f₀ (g * x) ∂μ) ^ (1 / 2 : ℝ) < _
    rw [hA1, hcancel, ← hηhalf]
    exact ENNReal.rpow_lt_rpow hb (by norm_num)
  have hClt : eLpNorm C 2 μ < ENNReal.ofReal (ε / 4) := by
    rw [hCdef, eLpNorm_indicator_eq_eLpNorm_restrict (hSxm.diff hD'm), heLp]
    show (∫⁻ g in Sx \ D', f₀ (g * x) ∂μ) ^ (1 / 2 : ℝ) < _
    rw [hC1, ← hηhalf]
    exact ENNReal.rpow_lt_rpow hb (by norm_num)
  have hBlt : eLpNorm Bf 2 μ < ENNReal.ofReal (ε / 4) := hB x hx₂

  rw [← hres, ← eLpNorm_indicator_eq_eLpNorm_restrict hD'm, hdecomp]
  calc eLpNorm (A + (Bf - C)) 2 μ ≤ eLpNorm A 2 μ + eLpNorm (Bf - C) 2 μ := eLpNorm_add_le hAm (hBm.sub hCm) one_le_two
    _ ≤ eLpNorm A 2 μ + (eLpNorm Bf 2 μ + eLpNorm C 2 μ) := by
        gcongr; exact eLpNorm_sub_le hBm hCm one_le_two
    _ < ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) :=
        ENNReal.add_lt_add hAlt (ENNReal.add_lt_add hBlt hClt)
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add hε4.le (by linarith)]; ring_nf
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

end S_AutomorphicForm_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain (solution)
