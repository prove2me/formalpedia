-- Prove2me | solution 1 for AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/531e2758-b204-5370-a927-5c4fd9b5d259

import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous
import Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
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
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
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
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (convOp K f u) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    isFiniteMeasure_restrict.2 hfin.ne

  have hLs : IsLsXiFunction (𝓞 K) K ⊤ ξK u ∧
      MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hu
  have hΓ := hLs.1.left_invariant
  have hZ := hLs.1.central_transform
  have hmeas : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hslab hFD ξK u _hu

  have hRc : Continuous (convOp K f u) :=
    AutomorphicForm.continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous K α β hα hαβ ξK hξc
      u _hu f _hf _hfc

  have hRΓ : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      convOp K f u (globalPoints (𝓞 K) K γ * x) = convOp K f u x := by
    intro γ x
    simp only [convOp_apply, rightConv_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show u (globalPoints (𝓞 K) K γ * x * g) * f g = u (x * g) * f g
    rw [mul_assoc, hΓ]
  have hRZ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) (x : AdelicGL2 (𝓞 K) K),
      convOp K f u (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * x) = ((ξK z : ℂˣ) : ℂ) * convOp K f u x := by
    intro z x
    simp only [convOp_apply, rightConv_apply]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show u (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * x * g) * f g = ((ξK z : ℂˣ) : ℂ) * (u (x * g) * f g)
    rw [mul_assoc, hZ z (x * g), mul_assoc]

  have hN : ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖u x‖ ^ 2)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ⊤ :=
    ((memLp_two_iff_integrable_sq_norm hmeas.restrict).1 hLs.2).lintegral_lt_top
  have hA : ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ⊤ := (_hf.integrable_of_hasCompactSupport _hfc).2

  have htrans : ∀ g : AdelicGL2 (𝓞 K) K,
      ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖u (x * g)‖ ^ 2)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖u x‖ ^ 2)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro g
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

  have hpw : ∀ x : AdelicGL2 (𝓞 K) K, ‖convOp K f u x‖ₑ ^ 2 ≤
      (∫⁻ g, ENNReal.ofReal (‖u (x * g)‖ ^ 2) * ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro x
    rw [convOp_apply, rightConv_apply]
    exact T6B.enorm_integral_mul_sq_le' _ (fun g => u (x * g)) f
      (hmeas.comp_quasiMeasurePreserving (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 K) K) x).quasiMeasurePreserving)
      _hf.aestronglyMeasurable

  have hq : Measure.QuasiMeasurePreserving (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => p.1 * p.2)
      (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod
        (adelicGLHaar (Fin 2) (𝓞 K) K)) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_mul ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))
        (adelicGLHaar (Fin 2) (𝓞 K) K)).quasiMeasurePreserving
  have hmeasP : AEMeasurable (Function.uncurry fun (x g : AdelicGL2 (𝓞 K) K) =>
      ENNReal.ofReal (‖u (x * g)‖ ^ 2) * ‖f g‖ₑ)
      (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod
        (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    have h1 : AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (p.1 * p.2))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod
          (adelicGLHaar (Fin 2) (𝓞 K) K)) := hmeas.comp_quasiMeasurePreserving hq
    exact ((h1.norm.aemeasurable.pow_const 2).ennreal_ofReal).mul
      ((_hf.comp continuous_snd).aestronglyMeasurable.enorm)

  have hbound : ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖convOp K f u x‖ ^ 2)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
      ((∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖u x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    calc ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖convOp K f u x‖ ^ 2)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        = ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ‖convOp K f u x‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_congr fun x => by rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫⁻ g, ENNReal.ofReal (‖u (x * g)‖ ^ 2) * ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_mono fun x => hpw x
      _ = (∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β,
            ∫⁻ g, ENNReal.ofReal (‖u (x * g)‖ ^ 2) * ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_mul_const' _ _ hA.ne
      _ = (∫⁻ g, ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β,
            ENNReal.ofReal (‖u (x * g)‖ ^ 2) * ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          rw [lintegral_lintegral_swap hmeasP]
      _ = (∫⁻ g, (∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖u x‖ ^ 2)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              ∫⁻ g, ‖f g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          congr 1
          refine lintegral_congr fun g => ?_
          rw [lintegral_mul_const' _ _ enorm_ne_top, htrans g]
      _ = _ := by rw [lintegral_const_mul' _ _ hN.ne]
  have hlt : ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β, ENNReal.ofReal (‖convOp K f u x‖ ^ 2)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hN hA) hA)
  have hMem : MemLp (convOp K f u) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    (memLp_two_iff_integrable_sq_norm hRc.aestronglyMeasurable).2
      ⟨(hRc.norm.pow 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).2 hlt⟩
  exact (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨hRΓ, hRZ⟩, hMem⟩

end S_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain (solution)
