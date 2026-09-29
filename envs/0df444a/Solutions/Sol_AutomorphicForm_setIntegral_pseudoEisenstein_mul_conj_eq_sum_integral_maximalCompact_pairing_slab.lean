-- Prove2me | solution 1 for AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c89063ae-2e8a-539b-906f-2eed43d72f82

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_HaarQuotient
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_pseudoEisenstein_eq_setIntegral_quotient_slab
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

section

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace MellinParseval

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

private theorem integral_sesq_fourier_fourier (M : E →L⋆[ℂ] F →L[ℂ] G) {a : ℝ → E} {b : ℝ → F}
    (ha : Integrable a) (hb : Integrable b) (hb' : Integrable (𝓕 b)) (hbc : Continuous b) :
    ∫ ξ : ℝ, M (𝓕 a ξ) (𝓕 b ξ) = ∫ t : ℝ, M (a t) (b t) := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (L := innerₗ ℝ) M
    continuous_fourierChar continuous_inner ha hb'
  rw [flip_innerₗ] at h
  have h' : ∫ ξ : ℝ, M (𝓕 a ξ) (𝓕 b ξ) = ∫ x : ℝ, M (a x) (𝓕⁻ (𝓕 b) x) := h
  rw [hbc.fourierInv_fourier_eq hb hb'] at h'
  exact h'

private theorem integral_sesq_fourierInv_fourierInv (M : E →L⋆[ℂ] F →L[ℂ] G) {a : ℝ → E} {b : ℝ → F}
    (ha : Integrable a) (hb : Integrable b) (hb' : Integrable (𝓕⁻ b)) (hbc : Continuous b) :
    ∫ ξ : ℝ, M (𝓕⁻ a ξ) (𝓕⁻ b ξ) = ∫ t : ℝ, M (a t) (b t) := by
  rw [fourierInv_eq_fourier_comp_neg a, fourierInv_eq_fourier_comp_neg b]
  have hb'' : Integrable (𝓕 fun x : ℝ => b (-x)) := by
    rw [← fourierInv_eq_fourier_comp_neg b]
    exact hb'
  rw [integral_sesq_fourier_fourier M ha.comp_neg hb.comp_neg hb'' (hbc.comp continuous_neg)]
  exact integral_neg_eq_self (fun t : ℝ => M (a t) (b t)) volume

private def lineProfile (σ : ℝ) (a : ℝ → E) (y : ℝ) : E :=
  ∫ t : ℝ, (((y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) • a t)

private def HasIntegrableProfile (σ : ℝ) (b : ℝ → F) : Prop :=
  IntegrableOn (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) • lineProfile σ b y) (Set.Ioi (0 : ℝ))

private def charIntegral (a : ℝ → E) (u : ℝ) : E :=
  ∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) • a t

private theorem cpow_exp_eq (σ u t : ℝ) :
    ((Real.exp u : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.exp (σ * u) : ℝ) : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_exp, mul_add, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul]
  congr 1 <;> (congr 1; ring)

omit [CompleteSpace E] in

private theorem lineProfile_exp (σ : ℝ) (a : ℝ → E) (u : ℝ) :
    lineProfile σ a (Real.exp u) = ((Real.exp (σ * u) : ℝ) : ℂ) • charIntegral a u := by
  unfold lineProfile charIntegral
  rw [← integral_smul]
  congr 1
  funext t
  rw [cpow_exp_eq, mul_smul]

omit [CompleteSpace E] in

private theorem charIntegral_two_pi_mul (a : ℝ → E) (w : ℝ) : charIntegral a (2 * π * w) = 𝓕⁻ a w := by
  rw [fourierInv_eq']
  unfold charIntegral
  have h : ∀ t : ℝ, ((t * (2 * π * w) : ℝ) : ℂ) = ((2 * π * inner ℝ t w : ℝ) : ℂ) := fun t => by
    rw [Real.inner_apply]
    push_cast
    ring
  simp_rw [h]

omit [CompleteSpace F] in

private theorem HasIntegrableProfile.integrable_fourierInv {σ : ℝ} {b : ℝ → F}
    (hbp : HasIntegrableProfile σ b) : Integrable (𝓕⁻ b) := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  have h1 := hbp
  unfold HasIntegrableProfile at h1
  rw [himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    integrableOn_univ] at h1
  have h2 : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u ^ (-σ) / Real.exp u : ℝ) : ℂ)) •
      lineProfile σ b (Real.exp u)) = charIntegral b u := by
    intro u
    rw [lineProfile_exp, ← Complex.coe_smul, smul_smul, smul_smul]
    have hs : |Real.exp u| * (Real.exp u ^ (-σ) / Real.exp u) * Real.exp (σ * u) = 1 := by
      rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
      simp only [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    have hsC : ((|Real.exp u| : ℝ) : ℂ) * ((Real.exp u ^ (-σ) / Real.exp u : ℝ) : ℂ) *
        ((Real.exp (σ * u) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hs
    rw [hsC, one_smul]
  simp_rw [h2] at h1
  have h3 : Integrable (fun w : ℝ => charIntegral b (2 * π * w)) := h1.comp_mul_left' h2π
  simpa only [charIntegral_two_pi_mul] using h3

private theorem integral_sesq_lineProfile_lineProfile (M : E →L⋆[ℂ] F →L[ℂ] G) (σ₁ σ₂ : ℝ)
    {a : ℝ → E} {b : ℝ → F} (ha : Integrable a) (hb : Integrable b) (hbc : Continuous b)
    (hbp : HasIntegrableProfile σ₂ b) :
    ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) • M (lineProfile σ₁ a y) (lineProfile σ₂ b y)
      = ((2 * π : ℝ) : ℂ) • ∫ t : ℝ, M (a t) (b t) := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  have hFb : Integrable (𝓕⁻ b) := hbp.integrable_fourierInv

  have hcollapse : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ)) •
      M (lineProfile σ₁ a (Real.exp u)) (lineProfile σ₂ b (Real.exp u)))
        = M (charIntegral a u) (charIntegral b u) := by
    intro u
    rw [lineProfile_exp, lineProfile_exp,
      map_smulₛₗ M ((Real.exp (σ₁ * u) : ℝ) : ℂ) (charIntegral a u), ContinuousLinearMap.smul_apply,
      map_smul (M (charIntegral a u)) ((Real.exp (σ₂ * u) : ℝ) : ℂ) (charIntegral b u),
      Complex.conj_ofReal, ← Complex.coe_smul, smul_smul, smul_smul, smul_smul]
    have hs : |Real.exp u| * (Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u) * Real.exp (σ₁ * u) *
        Real.exp (σ₂ * u) = 1 := by
      rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
      simp only [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    have hsC : ((|Real.exp u| : ℝ) : ℂ) * ((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ) *
        ((Real.exp (σ₁ * u) : ℝ) : ℂ) * ((Real.exp (σ₂ * u) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hs
    rw [hsC, one_smul]
  calc ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) •
          M (lineProfile σ₁ a y) (lineProfile σ₂ b y)
      = ∫ u : ℝ, M (charIntegral a u) (charIntegral b u) := by
        rw [himage, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
          Measure.restrict_univ]
        exact integral_congr_ae (Filter.Eventually.of_forall hcollapse)
    _ = |2 * π| • ∫ w : ℝ, M (charIntegral a (2 * π * w)) (charIntegral b (2 * π * w)) := by
        rw [Measure.integral_comp_mul_left (fun u : ℝ => M (charIntegral a u) (charIntegral b u))
            (2 * π),
          smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h2π), one_smul]
    _ = ((2 * π : ℝ) : ℂ) • ∫ t : ℝ, M (a t) (b t) := by
        simp_rw [charIntegral_two_pi_mul]
        rw [integral_sesq_fourierInv_fourierInv M ha hb hFb hbc, abs_of_pos (by positivity),
          Complex.coe_smul]

private theorem integral_sesq_lineProfile_lineProfile_neg (M : E →L⋆[ℂ] F →L[ℂ] G) (σ₁ σ₂ : ℝ)
    {a : ℝ → E} {b : ℝ → F} (ha : Integrable a) (hb : Integrable b) (hbc : Continuous b)
    (hbp : HasIntegrableProfile σ₂ (fun t : ℝ => b (-t))) :
    ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) •
        M (lineProfile σ₁ a y) (lineProfile σ₂ (fun t : ℝ => b (-t)) y)
      = ((2 * π : ℝ) : ℂ) • ∫ t : ℝ, M (a t) (b (-t)) :=
  integral_sesq_lineProfile_lineProfile M σ₁ σ₂ ha hb.comp_neg (hbc.comp continuous_neg) hbp

private theorem integral_conj_lineProfile_mul_lineProfile (σ₁ σ₂ : ℝ) {a b : ℝ → ℂ}
    (ha : Integrable a) (hb : Integrable b) (hbc : Continuous b) (hbp : HasIntegrableProfile σ₂ b) :
    ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) *
        (starRingEnd ℂ (lineProfile σ₁ a y) * lineProfile σ₂ b y)
      = ((2 * π : ℝ) : ℂ) * ∫ t : ℝ, starRingEnd ℂ (a t) * b t := by
  have h := integral_sesq_lineProfile_lineProfile (innerSL ℂ : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) σ₁ σ₂ ha hb hbc hbp
  simpa only [innerSL_apply_apply, RCLike.inner_apply', smul_eq_mul] using h

private theorem integrableOn_conj_lineProfile_mul_lineProfile (σ₁ σ₂ : ℝ) {a b : ℝ → ℂ}
    (ha : Integrable a) (hbp : HasIntegrableProfile σ₂ b) :
    IntegrableOn (fun y : ℝ => ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) *
        (starRingEnd ℂ (lineProfile σ₁ a y) * lineProfile σ₂ b y)) (Set.Ioi 0) := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  rw [himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    integrableOn_univ]
  have h2 : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ)) *
      (starRingEnd ℂ (lineProfile σ₁ a (Real.exp u)) * lineProfile σ₂ b (Real.exp u)))
        = starRingEnd ℂ (charIntegral a u) * charIntegral b u := by
    intro u
    rw [lineProfile_exp, lineProfile_exp, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal,
      ← Complex.coe_smul, smul_eq_mul]
    have hs : |Real.exp u| * (Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u) * Real.exp (σ₁ * u) *
        Real.exp (σ₂ * u) = 1 := by
      rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
      simp only [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    have hsC : ((|Real.exp u| : ℝ) : ℂ) * ((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ) *
        ((Real.exp (σ₁ * u) : ℝ) : ℂ) * ((Real.exp (σ₂ * u) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hs
    linear_combination (starRingEnd ℂ (charIntegral a u) * charIntegral b u) * hsC
  simp_rw [h2]
  refine (integrable_comp_mul_left_iff
    (fun u : ℝ => starRingEnd ℂ (charIntegral a u) * charIntegral b u) h2π).mp ?_
  simp only [charIntegral_two_pi_mul]
  have hFa : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ) a) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner.neg) ha
  have hcont : Continuous (𝓕⁻ a) := hFa
  refine Integrable.bdd_mul (c := ∫ t : ℝ, ‖a t‖) hbp.integrable_fourierInv
    ((Complex.continuous_conj.comp hcont).aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
  intro x
  rw [Complex.norm_conj]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (-innerₗ ℝ) a x

end MellinParseval

end

end

section

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace StripContour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_cpow_smul {y : ℝ} (hy : 0 < y) (x t : ℝ) (v : E) :
    ‖((y : ℂ) ^ ((x : ℂ) + (t : ℂ) * Complex.I)) • v‖ = y ^ x * ‖v‖ := by
  have hre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by simp
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]

private theorem rpow_le_add_of_mem_uIcc {y : ℝ} (hy : 0 < y) {c d x : ℝ} (hx : x ∈ Set.uIcc c d) :
    y ^ x ≤ y ^ c + y ^ d := by
  have hc : 0 ≤ y ^ c := (Real.rpow_pos_of_pos hy c).le
  have hd : 0 ≤ y ^ d := (Real.rpow_pos_of_pos hy d).le
  rcases Set.mem_uIcc.1 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rcases le_or_gt 1 y with hy1 | hy1
    · exact (Real.rpow_le_rpow_of_exponent_le hy1 h₂).trans (le_add_of_nonneg_left hc)
    · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1.le h₁).trans (le_add_of_nonneg_right hd)
  · rcases le_or_gt 1 y with hy1 | hy1
    · exact (Real.rpow_le_rpow_of_exponent_le hy1 h₂).trans (le_add_of_nonneg_right hd)
    · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1.le h₁).trans (le_add_of_nonneg_left hc)

private theorem
rpow_le_add_of_mem_Icc {c d y : ℝ} (hc : 0 < c) (hy : y ∈ Set.Icc c d) (σ : ℝ) : y ^ σ ≤ c ^ σ + d ^ σ := by
  have hc' : 0 ≤ c ^ σ := (Real.rpow_pos_of_pos hc σ).le
  have hd' : 0 ≤ d ^ σ := (Real.rpow_pos_of_pos (hc.trans_le (hy.1.trans hy.2)) σ).le
  rcases le_or_gt 0 σ with hσ | hσ
  · exact (Real.rpow_le_rpow (hc.le.trans hy.1) hy.2 hσ).trans (le_add_of_nonneg_left hc')
  · exact (Real.rpow_le_rpow_of_nonpos hc hy.1 hσ.le).trans (le_add_of_nonneg_right hd')

private theorem abs_sub_lt_of_mem_uIcc {σ σ₀ σ₁ σ₂ x : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀)
    (hx : x ∈ Set.uIcc σ₁ σ₂) : |x - σ| < σ₀ := by
  rw [abs_sub_lt_iff] at h₁ h₂ ⊢
  rcases Set.mem_uIcc.1 hx with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

section Strip

variable {f : ℂ → E} {σ σ₀ : ℝ} {m : ℝ → ℝ}

private theorem continuous_line (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) :
    Continuous fun t : ℝ => f ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
  have hline : Continuous fun t : ℝ => (σ' : ℂ) + (t : ℂ) * Complex.I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine hf.continuousOn.comp_continuous hline fun t => ?_
  simpa using hσ'

private theorem integrable_kernel_line (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ => ((y : ℂ) ^ ((σ' : ℂ) + (t : ℂ) * Complex.I)) • f ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
  refine (hm.const_mul (y ^ σ')).mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hk : Continuous fun t : ℝ => (y : ℂ) ^ ((σ' : ℂ) + (t : ℂ) * Complex.I) :=
      continuous_const.cpow (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        fun _ => Complex.ofReal_mem_slitPlane.2 hy
    exact (hk.smul (continuous_line hf hσ')).aestronglyMeasurable
  · rw [norm_cpow_smul hy]
    exact mul_le_mul_of_nonneg_left (hbound σ' hσ' t) (Real.rpow_pos_of_pos hy σ').le

private theorem
norm_horizontal_le (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ₁ σ₂ : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀) {y : ℝ} (hy : 0 < y) (c : ℝ) :
    ‖∫ x : ℝ in σ₁..σ₂, ((y : ℂ) ^ ((x : ℂ) + (c : ℂ) * Complex.I)) • f ((x : ℂ) + (c : ℂ) * Complex.I)‖
      ≤ (y ^ σ₁ + y ^ σ₂) * m c * |σ₂ - σ₁| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  have hx' : x ∈ Set.uIcc σ₁ σ₂ := Set.uIoc_subset_uIcc hx
  rw [norm_cpow_smul hy]
  exact mul_le_mul (rpow_le_add_of_mem_uIcc hy hx') (hbound x (abs_sub_lt_of_mem_uIcc h₁ h₂ hx') c)
    (norm_nonneg _) (by positivity)

private theorem norm_truncated_sub_le (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀})
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ₁ σ₂ : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    ‖(∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I))
        - ∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (y ^ σ₁ + y ^ σ₂) * (m a + m b) * |σ₂ - σ₁| := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hg : DifferentiableOn ℂ (fun s : ℂ => ((y : ℂ) ^ s) • f s) {s : ℂ | |s.re - σ| < σ₀} :=
    (differentiableOn_id.const_cpow (Or.inl hy0)).smul hf
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s : ℂ => ((y : ℂ) ^ s) • f s)
    ⟨σ₁, a⟩ ⟨σ₂, b⟩ (hg.mono fun s hs => abs_sub_lt_of_mem_uIcc h₁ h₂ (Complex.mem_reProdIm.1 hs).1)
  dsimp only at hrect
  set Ha := ∫ x : ℝ in σ₁..σ₂, ((y : ℂ) ^ ((x : ℂ) + (a : ℂ) * Complex.I)) • f ((x : ℂ) + (a : ℂ) * Complex.I)
    with hHa
  set Hb := ∫ x : ℝ in σ₁..σ₂, ((y : ℂ) ^ ((x : ℂ) + (b : ℂ) * Complex.I)) • f ((x : ℂ) + (b : ℂ) * Complex.I)
    with hHb
  set V₂ := ∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I)
    with hV₂
  set V₁ := ∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)
    with hV₁
  have hV : Complex.I • (V₂ - V₁) = Hb - Ha := by
    rw [smul_sub, ← sub_eq_zero, ← hrect]
    abel
  have hnorm : ‖V₂ - V₁‖ = ‖Hb - Ha‖ := by
    rw [← hV, norm_smul, Complex.norm_I, one_mul]
  rw [hnorm]
  calc ‖Hb - Ha‖ ≤ ‖Hb‖ + ‖Ha‖ := norm_sub_le _ _
    _ ≤ (y ^ σ₁ + y ^ σ₂) * m b * |σ₂ - σ₁| + (y ^ σ₁ + y ^ σ₂) * m a * |σ₂ - σ₁| :=
        add_le_add (norm_horizontal_le hbound h₁ h₂ hy b) (norm_horizontal_le hbound h₁ h₂ hy a)
    _ = (y ^ σ₁ + y ^ σ₂) * (m a + m b) * |σ₂ - σ₁| := by ring

private theorem exists_le_and_norm_lt {M : ℝ → ℝ} (hM : Integrable M) (T₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, T₀ ≤ T ∧ ‖M T‖ < ε := by
  by_contra hcon
  have hall : ∀ T : ℝ, T₀ ≤ T → ε ≤ ‖M T‖ := fun T hT => not_lt.1 fun h => hcon ⟨T, hT, h⟩
  have hsub : Set.Ici T₀ ⊆ {T : ℝ | ε ≤ ‖M T‖} := fun T hT => hall T hT
  have hfin := hM.measure_norm_ge_lt_top hε
  have hle := measure_mono (μ := (volume : Measure ℝ)) hsub
  rw [Real.volume_Ici] at hle
  exact lt_irrefl _ (lt_of_le_of_lt hle hfin)

private theorem lineProfile_eq_of_abs_sub_lt (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ₁ σ₂ : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    MellinParseval.lineProfile σ₁ (fun t : ℝ => f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) y
      = MellinParseval.lineProfile σ₂ (fun t : ℝ => f ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) y := by
  unfold MellinParseval.lineProfile
  beta_reduce
  set L₁ := ∫ t : ℝ, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I) with hL₁
  set L₂ := ∫ t : ℝ, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I) with hL₂

  set D : ℝ → E := fun T =>
    (∫ t : ℝ in (-T)..T, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I))
      - ∫ t : ℝ in (-T)..T, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)
    with hD
  have hconv : Tendsto D atTop (𝓝 (L₂ - L₁)) :=
    (intervalIntegral_tendsto_integral (integrable_kernel_line hf hm hbound h₂ hy) tendsto_neg_atTop_atBot
        tendsto_id).sub
      (intervalIntegral_tendsto_integral (integrable_kernel_line hf hm hbound h₁ hy) tendsto_neg_atTop_atBot
        tendsto_id)

  set M : ℝ → ℝ := fun T => (y ^ σ₁ + y ^ σ₂) * |σ₂ - σ₁| * (m (-T) + m T) with hM
  have hMint : Integrable M := (hm.comp_neg.add hm).const_mul _
  have hDle : ∀ T : ℝ, ‖D T‖ ≤ M T := fun T =>
    (norm_truncated_sub_le hf hbound h₁ h₂ hy (-T) T).trans_eq (by simp only [hM]; ring)

  rw [eq_comm, ← sub_eq_zero]
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hconv) (ε / 2) (by positivity))
  obtain ⟨T, hTT₀, hMT⟩ := exists_le_and_norm_lt hMint T₀ (show (0 : ℝ) < ε / 2 by positivity)
  have hdist : ‖L₂ - L₁ - D T‖ < ε / 2 := by
    have := hT₀ T hTT₀
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at this
  have htri : ‖L₂ - L₁‖ ≤ ‖L₂ - L₁ - D T‖ + ‖D T‖ := by
    calc ‖L₂ - L₁‖ = ‖(L₂ - L₁ - D T) + D T‖ := by rw [sub_add_cancel]
      _ ≤ ‖L₂ - L₁ - D T‖ + ‖D T‖ := norm_add_le _ _
  have hMabs : M T ≤ ‖M T‖ := le_abs_self (M T)
  linarith [hDle T]

private theorem
lineProfile_eq_lineProfile_of_mem_Ioo (hσ₀ : 0 < σ₀) (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀})
    (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {y : ℝ} (hy : 0 < y) {σ' : ℝ} (hσ' : σ' ∈ Set.Ioo (σ - σ₀) (σ + σ₀)) :
    MellinParseval.lineProfile σ' (fun t : ℝ => f ((σ' : ℂ) + (t : ℂ) * Complex.I)) y
      = MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y := by
  have h' : |σ' - σ| < σ₀ := by
    rw [abs_sub_lt_iff]
    exact ⟨by linarith [hσ'.2], by linarith [hσ'.1]⟩
  have h0 : |σ - σ| < σ₀ := by simpa using hσ₀
  exact lineProfile_eq_of_abs_sub_lt hf hm hbound h' h0 hy

private theorem norm_lineProfile_le (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    (hσσ : |σ - σ| < σ₀) {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    ‖MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y‖ ≤ y ^ σ' * ∫ t : ℝ, m t := by
  rw [lineProfile_eq_of_abs_sub_lt hf hm hbound hσσ hσ' hy]
  unfold MellinParseval.lineProfile
  beta_reduce
  refine (norm_integral_le_of_norm_le (hm.const_mul (y ^ σ')) (Eventually.of_forall fun t => ?_)).trans_eq
    (integral_const_mul _ _)
  rw [norm_cpow_smul hy]
  exact mul_le_mul_of_nonneg_left (hbound σ' hσ' t) (Real.rpow_pos_of_pos hy σ').le

private theorem continuousOn_lineProfile (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    (hσσ : |σ - σ| < σ₀) :
    ContinuousOn (fun y : ℝ => MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y)
      (Set.Ioi 0) := by
  unfold MellinParseval.lineProfile
  beta_reduce
  have hIcc : ∀ c d : ℝ, 0 < c → c ≤ d →
      ContinuousOn (fun y : ℝ => ∫ t : ℝ, ((y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) •
        f ((σ : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc c d) := by
    intro c d hc hcd
    refine continuousOn_of_dominated (bound := fun t => (c ^ σ + d ^ σ) * m t) ?_ ?_ (hm.const_mul _) ?_
    · intro y hy
      exact (integrable_kernel_line hf hm hbound hσσ (hc.trans_le hy.1)).aestronglyMeasurable
    · intro y hy
      refine Eventually.of_forall fun t => ?_
      rw [norm_cpow_smul (hc.trans_le hy.1)]
      exact mul_le_mul (rpow_le_add_of_mem_Icc hc hy σ) (hbound σ hσσ t) (norm_nonneg _)
        (add_nonneg (Real.rpow_pos_of_pos hc σ).le (Real.rpow_pos_of_pos (hc.trans_le hcd) σ).le)
    · refine Eventually.of_forall fun t => ?_
      exact (Complex.continuous_ofReal.continuousOn.cpow continuousOn_const fun y hy =>
        Complex.ofReal_mem_slitPlane.2 (hc.trans_le hy.1)).smul continuousOn_const
  intro y hy
  have hy' : (0 : ℝ) < y := hy
  exact ((hIcc (y / 2) (2 * y) (by positivity) (by linarith)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

private theorem rpow_neg_div_mul_rpow {y : ℝ} (hy : 0 < y) (σ σ' : ℝ) : y ^ (-σ) / y * y ^ σ' = y ^ (σ' - σ - 1) := by
  rw [Real.rpow_sub_one hy.ne', Real.rpow_sub hy, Real.rpow_neg hy.le]
  ring

private theorem norm_smul_lineProfile_le (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    (hσσ : |σ - σ| < σ₀) {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    ‖((y ^ (-σ) / y : ℝ) : ℂ) •
        MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y‖
      ≤ (∫ t : ℝ, m t) * y ^ (σ' - σ - 1) := by
  have hr : 0 < y ^ (-σ) / y := by positivity
  rw [norm_smul, Complex.norm_of_nonneg hr.le]
  calc y ^ (-σ) / y * ‖MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y‖
      ≤ y ^ (-σ) / y * (y ^ σ' * ∫ t : ℝ, m t) :=
        mul_le_mul_of_nonneg_left (norm_lineProfile_le hf hm hbound hσσ hσ' hy) hr.le
    _ = (∫ t : ℝ, m t) * y ^ (σ' - σ - 1) := by rw [← rpow_neg_div_mul_rpow hy σ σ']; ring

private theorem hasIntegrableProfile_of_differentiableOn (hσ₀ : 0 < σ₀)
    (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t) :
    MellinParseval.HasIntegrableProfile σ fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hσσ : |σ - σ| < σ₀ := by simpa using hσ₀
  have hσp : |σ + σ₀ / 2 - σ| < σ₀ := by
    rw [abs_sub_lt_iff]; constructor <;> linarith
  have hσm : |σ - σ₀ / 2 - σ| < σ₀ := by
    rw [abs_sub_lt_iff]; constructor <;> linarith
  have hcont := continuousOn_lineProfile hf hm hbound hσσ

  have hmeas : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioi 0 →
      AEStronglyMeasurable (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) •
        MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y) (volume.restrict s) := by
    intro s hs hs0
    refine AEStronglyMeasurable.smul ?_ ((hcont.mono hs0).aestronglyMeasurable hs)
    exact (Complex.measurable_ofReal.comp ((measurable_id.pow_const (-σ)).div measurable_id)).aestronglyMeasurable
  unfold MellinParseval.HasIntegrableProfile
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  ·
    have hint : IntegrableOn (fun y : ℝ => (∫ t : ℝ, m t) * y ^ (σ + σ₀ / 2 - σ - 1)) (Set.Ioc (0 : ℝ) 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    refine hint.mono' (hmeas _ measurableSet_Ioc Set.Ioc_subset_Ioi_self) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => norm_smul_lineProfile_le hf hm hbound hσσ hσp hy.1
  ·
    have hint : IntegrableOn (fun y : ℝ => (∫ t : ℝ, m t) * y ^ (σ - σ₀ / 2 - σ - 1)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hint.mono' (hmeas _ measurableSet_Ioi fun y hy => Set.mem_Ioi.2 (zero_lt_one.trans (Set.mem_Ioi.1 hy))) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
      norm_smul_lineProfile_le hf hm hbound hσσ hσm (zero_lt_one.trans (Set.mem_Ioi.1 hy))

end Strip

end StripContour

end

end

section

open MeasureTheory

namespace InvariantDescent

variable {G : Type*} [Group G] {H : Subgroup G}

private def descend {β : Type*} (f : G → β) (hf : ∀ x ∈ H, ∀ g, f (x * g) = f g) :
    MulAction.orbitRel.Quotient H G → β :=
  Quotient.lift f (fun a b hab => by
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hx]
    exact hf x x.2 b)

private theorem apply_out_eq_descend {β : Type*} (f : G → β) (hf : ∀ x ∈ H, ∀ g, f (x * g) = f g)
    (q : MulAction.orbitRel.Quotient H G) : f q.out = descend f hf q := by
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.mk_out (s := MulAction.orbitRel H G) g))
    show f (Quotient.mk (MulAction.orbitRel H G) g).out = f g
    rw [← hx]
    exact hf x x.2 g

variable [MeasurableSpace G]

private theorem measurable_descend {β : Type*} [MeasurableSpace β] (f : G → β)
    (hf : ∀ x ∈ H, ∀ g, f (x * g) = f g) (hfm : Measurable f) : Measurable (descend f hf) :=
  measurable_from_quotient.mpr hfm

private theorem map_descend_eq {m : Measure (MulAction.orbitRel.Quotient H G)} {ρ : Measure G}
    (hdis : ∀ f : G → ENNReal, Measurable f → (∀ x ∈ H, ∀ g, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂m = ∫⁻ g, f g ∂ρ)
    {β : Type*} [MeasurableSpace β] (F : G → β) (hFm : Measurable F)
    (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    m.map (descend F hFinv) = ρ.map F := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_descend F hFinv hFm) hs, Measure.map_apply hFm hs,
    ← lintegral_indicator_one ((measurable_descend F hFinv hFm) hs),
    ← lintegral_indicator_one (hFm hs)]
  have hind : ∀ x ∈ H, ∀ g, (F ⁻¹' s).indicator (1 : G → ENNReal) (x * g) = (F ⁻¹' s).indicator 1 g := by
    intro x hx g
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, hFinv x hx g]
  rw [← hdis _ (measurable_one.indicator (hFm hs)) hind]
  refine lintegral_congr (fun q => ?_)
  simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, apply_out_eq_descend F hFinv q]

private theorem integral_apply_out_eq {m : Measure (MulAction.orbitRel.Quotient H G)} {ρ : Measure G}
    (hdis : ∀ f : G → ENNReal, Measurable f → (∀ x ∈ H, ∀ g, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂m = ∫⁻ g, f g ∂ρ)
    (F : G → ℂ) (hFm : Measurable F) (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    ∫ q, F q.out ∂m = ∫ g, F g ∂ρ := by
  have hmap := map_descend_eq hdis F hFm hFinv
  have h1 : ∫ z, (id z : ℂ) ∂(m.map (descend F hFinv)) = ∫ q, F q.out ∂m := by
    rw [integral_map (measurable_descend F hFinv hFm).aemeasurable aestronglyMeasurable_id]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => (apply_out_eq_descend F hFinv q).symm)
  have h2 : ∫ z, (id z : ℂ) ∂(ρ.map F) = ∫ g, F g ∂ρ := by
    rw [integral_map hFm.aemeasurable aestronglyMeasurable_id]
    rfl
  rw [← h1, ← h2, hmap]

private theorem integrable_apply_out_iff {m : Measure (MulAction.orbitRel.Quotient H G)} {ρ : Measure G}
    (hdis : ∀ f : G → ENNReal, Measurable f → (∀ x ∈ H, ∀ g, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂m = ∫⁻ g, f g ∂ρ)
    (F : G → ℂ) (hFm : Measurable F) (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    Integrable (fun q => F q.out) m ↔ Integrable F ρ := by
  have hmap := map_descend_eq hdis F hFm hFinv
  have h1 : Integrable (fun q => F q.out) m ↔ Integrable (descend F hFinv) m :=
    integrable_congr (Filter.Eventually.of_forall fun q => apply_out_eq_descend F hFinv q)
  have h2 : Integrable (descend F hFinv) m ↔ Integrable (id : ℂ → ℂ) (m.map (descend F hFinv)) :=
    (integrable_map_measure aestronglyMeasurable_id (measurable_descend F hFinv hFm).aemeasurable).symm
  have h3 : Integrable F ρ ↔ Integrable (id : ℂ → ℂ) (ρ.map F) :=
    (integrable_map_measure aestronglyMeasurable_id hFm.aemeasurable).symm
  rw [h1, h2, h3, hmap]

private theorem measurable_apply_out {β : Type*} [MeasurableSpace β] (F : G → β) (hFm : Measurable F)
    (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => F q.out := by
  have h : (fun q : MulAction.orbitRel.Quotient H G => F q.out) = descend F hFinv :=
    funext fun q => apply_out_eq_descend F hFinv q
  rw [h]
  exact measurable_descend F hFinv hFm

end InvariantDescent

end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace IteratedCoordinates

variable {X Y Z G : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace G]

private def coordMeasure (μ₁ : Measure X) (μ₂ : Measure Y) (μ₃ : Measure Z) (w : Y → ℝ≥0∞)
    (π : X × Y × Z → G) : Measure G :=
  (μ₁.prod ((μ₂.withDensity w).prod μ₃)).map π

variable (μ₁ : Measure X) (μ₂ : Measure Y) (μ₃ : Measure Z) [SFinite μ₁] [SFinite μ₂] [SFinite μ₃]

omit [SFinite μ₁] in

private theorem lintegral_coordMeasure {w : Y → ℝ≥0∞} (hw : Measurable w) {π : X × Y × Z → G}
    (hπ : Measurable π) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂(coordMeasure μ₁ μ₂ μ₃ w π) = ∫⁻ x, ∫⁻ y, ∫⁻ z, f (π (x, y, z)) * w y ∂μ₃ ∂μ₂ ∂μ₁ := by
  unfold coordMeasure
  rw [lintegral_map hf hπ]
  have h1 : ∫⁻ p, f (π p) ∂(μ₁.prod ((μ₂.withDensity w).prod μ₃))
      = ∫⁻ x, ∫⁻ p, f (π (x, p)) ∂((μ₂.withDensity w).prod μ₃) ∂μ₁ :=
    lintegral_prod (fun p => f (π p)) (hf.comp hπ).aemeasurable
  rw [h1]
  refine lintegral_congr (fun x => ?_)
  have hx : Measurable fun p : Y × Z => f (π (x, p)) := (hf.comp hπ).comp measurable_prodMk_left
  have h2 : ∫⁻ p, f (π (x, p)) ∂((μ₂.withDensity w).prod μ₃)
      = ∫⁻ y, ∫⁻ z, f (π (x, y, z)) ∂μ₃ ∂(μ₂.withDensity w) :=
    lintegral_prod (fun p : Y × Z => f (π (x, p))) hx.aemeasurable
  have h3 : ∫⁻ y, ∫⁻ z, f (π (x, y, z)) ∂μ₃ ∂(μ₂.withDensity w)
      = ∫⁻ y, (w * fun y => ∫⁻ z, f (π (x, y, z)) ∂μ₃) y ∂μ₂ :=
    lintegral_withDensity_eq_lintegral_mul μ₂ hw hx.lintegral_prod_right'
  rw [h2, h3]
  refine lintegral_congr (fun y => ?_)
  have hxy : Measurable fun z : Z => f (π (x, y, z)) := hx.comp measurable_prodMk_left
  show w y * ∫⁻ z, f (π (x, y, z)) ∂μ₃ = ∫⁻ z, f (π (x, y, z)) * w y ∂μ₃
  rw [lintegral_mul_const _ hxy, mul_comm]

private theorem integral_coordMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : Y → ℝ≥0∞} (hw : Measurable w) (hwfin : ∀ y, w y < ∞) {π : X × Y × Z → G}
    (hπ : Measurable π) {F : G → E} (hFm : AEStronglyMeasurable F (coordMeasure μ₁ μ₂ μ₃ w π))
    (hFi : Integrable F (coordMeasure μ₁ μ₂ μ₃ w π)) :
    ∫ g, F g ∂(coordMeasure μ₁ μ₂ μ₃ w π)
      = ∫ x, ∫ y, (w y).toReal • ∫ z, F (π (x, y, z)) ∂μ₃ ∂μ₂ ∂μ₁ := by
  have hFi' : Integrable (fun p : X × Y × Z => F (π p)) (μ₁.prod ((μ₂.withDensity w).prod μ₃)) :=
    (integrable_map_measure hFm hπ.aemeasurable).mp hFi
  unfold coordMeasure
  rw [integral_map hπ.aemeasurable hFm, integral_prod _ hFi']
  refine integral_congr_ae ((hFi'.prod_right_ae).mono fun x hx => ?_)
  dsimp only at hx ⊢
  rw [integral_prod _ hx,
    integral_withDensity_eq_integral_toReal_smul hw (Filter.Eventually.of_forall hwfin) _]

omit [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] in

private theorem integrable_coordMeasure_of_norm_le {E : Type*} [NormedAddCommGroup E]
    {w : Y → ℝ≥0∞} {π : X × Y × Z → G} (hπ : Measurable π) {F : G → E}
    (hFm : AEStronglyMeasurable F (coordMeasure μ₁ μ₂ μ₃ w π)) {B : X × Y × Z → ℝ}
    (hB : Integrable B (μ₁.prod ((μ₂.withDensity w).prod μ₃))) (hle : ∀ p, ‖F (π p)‖ ≤ B p) :
    Integrable F (coordMeasure μ₁ μ₂ μ₃ w π) :=
  (integrable_map_measure hFm hπ.aemeasurable).mpr
    (hB.mono' (hFm.comp_aemeasurable hπ.aemeasurable) (Filter.Eventually.of_forall hle))

omit [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] in

private theorem aestronglyMeasurable_coordMeasure {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [SecondCountableTopology E] [OpensMeasurableSpace E]
    {w : Y → ℝ≥0∞} {π : X × Y × Z → G} {F : G → E} (hF : Measurable F) :
    AEStronglyMeasurable F (coordMeasure μ₁ μ₂ μ₃ w π) :=
  hF.aestronglyMeasurable

end IteratedCoordinates

end

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace IwasawaBochner

variable (K : Type) [Field K] [NumberField K]

private abbrev iwasawaCoord (p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K) :
    AdelicGL2 (𝓞 K) K :=
  centralScalar (𝓞 K) K p.1 * diagOne p.2.1 * (p.2.2 : AdelicGL2 (𝓞 K) K)

private abbrev torusWeight (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

private def iwasawaMeasure (D D' : Set (AdeleRing (𝓞 K) K)ˣ) : Measure (AdelicGL2 (𝓞 K) K) :=
  IteratedCoordinates.coordMeasure ((NumberField.Idele.idelicHaar K).restrict D)
    ((NumberField.Idele.idelicHaar K).restrict D') (maximalCompactHaar K) (torusWeight K)
    (iwasawaCoord K)

private def HasIwasawaDisintegration (cQ : ℝ≥0∞) (D D' : Set (AdeleRing (𝓞 K) K)ˣ) : Prop :=
  ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
    (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      cQ * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)

variable {K}

private theorem measurable_torusWeight (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) :
    Measurable (torusWeight K) :=
  ENNReal.measurable_ofReal.comp hnorm.inv

variable {D D' : Set (AdeleRing (𝓞 K) K)ˣ}

private theorem lintegral_iwasawaMeasure [SFinite (NumberField.Idele.idelicHaar K)]
    (hπ : Measurable (iwasawaCoord K)) (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K))
    {f : AdelicGL2 (𝓞 K) K → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂(iwasawaMeasure K D D') =
      ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
          f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) :=
  IteratedCoordinates.lintegral_coordMeasure ((NumberField.Idele.idelicHaar K).restrict D)
    ((NumberField.Idele.idelicHaar K).restrict D') (maximalCompactHaar K)
    (measurable_torusWeight hnorm) hπ hf

private theorem integrable_iwasawaMeasure_of_norm_le (hπ : Measurable (iwasawaCoord K))
    {Fc : AdelicGL2 (𝓞 K) K → ℂ} (hFm : Measurable Fc)
    {B : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℝ}
    (hB : Integrable B (((NumberField.Idele.idelicHaar K).restrict D).prod
      ((((NumberField.Idele.idelicHaar K).restrict D').withDensity (torusWeight K)).prod
        (maximalCompactHaar K))))
    (hle : ∀ p, ‖Fc (iwasawaCoord K p)‖ ≤ B p) :
    Integrable Fc (iwasawaMeasure K D D') :=
  IteratedCoordinates.integrable_coordMeasure_of_norm_le _ _ _ hπ hFm.aestronglyMeasurable hB hle

variable {cQ : ℝ≥0∞}

private theorem lintegral_out_eq_lintegral_smul_iwasawaMeasure [SFinite (NumberField.Idele.idelicHaar K)]
    (hdis : HasIwasawaDisintegration K cQ D D') (hπ : Measurable (iwasawaCoord K))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hf : Measurable f)
    (hfinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      ∫⁻ g, f g ∂(cQ • iwasawaMeasure K D D') := by
  have h1 : ∫⁻ g, f g ∂(cQ • iwasawaMeasure K D D') = cQ * ∫⁻ g, f g ∂(iwasawaMeasure K D D') :=
    lintegral_smul_measure cQ f
  rw [h1, lintegral_iwasawaMeasure hπ hnorm hf, hdis f hf hfinv]

private theorem integral_out_eq_smul_integral_iwasawa [SFinite (NumberField.Idele.idelicHaar K)]
    (hdis : HasIwasawaDisintegration K cQ D D') (hπ : Measurable (iwasawaCoord K))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) (Fc : AdelicGL2 (𝓞 K) K → ℂ)
    (hFm : Measurable Fc)
    (hFinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, Fc (x * g) = Fc g)
    (hFi : Integrable Fc (iwasawaMeasure K D D')) :
    ∫ q, Fc q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      cQ.toReal • ∫ z in D, ∫ t in D',
        (ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)).toReal •
          ∫ k, Fc (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  rw [InvariantDescent.integral_apply_out_eq
      (lintegral_out_eq_lintegral_smul_iwasawaMeasure hdis hπ hnorm) Fc hFm hFinv,
    integral_smul_measure]
  congr 1
  exact IteratedCoordinates.integral_coordMeasure ((NumberField.Idele.idelicHaar K).restrict D)
    ((NumberField.Idele.idelicHaar K).restrict D') (maximalCompactHaar K)
    (measurable_torusWeight hnorm) (fun _ => ENNReal.ofReal_lt_top) hπ hFm.aestronglyMeasurable
    hFi

private theorem integrable_apply_out [SFinite (NumberField.Idele.idelicHaar K)]
    (hdis : HasIwasawaDisintegration K cQ D D') (hπ : Measurable (iwasawaCoord K))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) (hcQ : cQ ≠ ∞)
    (Fc : AdelicGL2 (𝓞 K) K → ℂ) (hFm : Measurable Fc)
    (hFinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, Fc (x * g) = Fc g)
    (hFi : Integrable Fc (iwasawaMeasure K D D')) :
    Integrable (fun q => Fc q.out) (rationalTorusUnipotentQuotientMeasure K) :=
  (InvariantDescent.integrable_apply_out_iff
      (lintegral_out_eq_lintegral_smul_iwasawaMeasure hdis hπ hnorm) Fc hFm hFinv).mpr
    (hFi.smul_measure hcQ)

end IwasawaBochner

end

end

section

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace NormWindowVolume

private def window (d₁ d₂ y : ℝ) : Set ℝ := {r : ℝ | r ^ 2 * y ∈ Set.Icc d₁ d₂}

private theorem measurableSet_window (d₁ d₂ y : ℝ) : MeasurableSet (window d₁ d₂ y) :=
  (by fun_prop : Measurable fun r : ℝ => r ^ 2 * y) measurableSet_Icc

private theorem window_inter_Ioi {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hy : 0 < y) :
    window d₁ d₂ y ∩ Set.Ioi 0 = Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y)) := by
  ext r
  simp only [window, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hr⟩
    have hd₂y : 0 ≤ d₂ / y := (div_pos (hd₁.trans_le (h₁.trans h₂)) hy).le
    refine ⟨?_, ?_⟩
    · conv_rhs => rw [← Real.sqrt_sq hr.le]
      rw [Real.sqrt_le_sqrt_iff (sq_nonneg r), div_le_iff₀ hy]
      exact h₁
    · conv_lhs => rw [← Real.sqrt_sq hr.le]
      rw [Real.sqrt_le_sqrt_iff hd₂y, le_div_iff₀ hy]
      exact h₂
  · rintro ⟨h₁, h₂⟩
    have hr : 0 < r := (Real.sqrt_pos.mpr (div_pos hd₁ hy)).trans_le h₁
    have hd₂y : 0 ≤ d₂ / y := (Real.sqrt_pos.mp (hr.trans_le h₂)).le
    rw [← Real.sqrt_sq hr.le, Real.sqrt_le_sqrt_iff (sq_nonneg r), div_le_iff₀ hy] at h₁
    rw [← Real.sqrt_sq hr.le, Real.sqrt_le_sqrt_iff hd₂y, le_div_iff₀ hy] at h₂
    exact ⟨⟨h₁, h₂⟩, hr⟩

private theorem lintegral_window_inv {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    ∫⁻ r in Set.Ioi (0 : ℝ), (window d₁ d₂ y).indicator (fun _ => (1 : ℝ≥0∞)) r * ENNReal.ofReal r⁻¹
      = ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  have hd₂ : 0 < d₂ := hd₁.trans_le hd
  have ha : 0 < Real.sqrt (d₁ / y) := Real.sqrt_pos.mpr (div_pos hd₁ hy)
  have hab : Real.sqrt (d₁ / y) ≤ Real.sqrt (d₂ / y) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hd hy.le)
  have hb : 0 < Real.sqrt (d₂ / y) := ha.trans_le hab
  have hfun : ∀ r : ℝ, (window d₁ d₂ y).indicator (fun _ => (1 : ℝ≥0∞)) r * ENNReal.ofReal r⁻¹
      = (window d₁ d₂ y).indicator (fun r => ENNReal.ofReal r⁻¹) r := by
    intro r
    by_cases hr : r ∈ window d₁ d₂ y <;> simp [hr]
  simp_rw [hfun]
  rw [lintegral_indicator (measurableSet_window d₁ d₂ y), Measure.restrict_restrict (measurableSet_window d₁ d₂ y),
    window_inter_Ioi hd₁ hy]
  have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))) :=
    (continuousOn_inv₀.mono fun r hr => (ha.trans_le (Set.mem_Icc.mp hr).1).ne').integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => inv_nonneg.mpr (ha.trans_le hr.1).le)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb,
    Real.log_div hb.ne' ha.ne', Real.log_sqrt (div_pos hd₂ hy).le, Real.log_sqrt (div_pos hd₁ hy).le,
    Real.log_div hd₂.ne' hy.ne', Real.log_div hd₁.ne' hy.ne', Real.log_div hd₂.ne' hd₁.ne']
  ring

variable {F : Type} [Field F] [NumberField F]

private theorem lintegral_indicator_window {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    ∫⁻ z in D, (window d₁ d₂ y).indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F)
      = V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  rw [hV ((window d₁ d₂ y).indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator (measurableSet_window d₁ d₂ y)),
    lintegral_window_inv hd₁ hd hy]

private theorem measure_window {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    NumberField.Idele.idelicHaar F ({z | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂} ∩ D)
      = V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  have hpre : MeasurableSet {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂} :=
    (continuous_ideleNorm F).measurable (measurableSet_window d₁ d₂ y)
  rw [← Measure.restrict_apply hpre, ← lintegral_indicator_one hpre, ← lintegral_indicator_window hV hd₁ hd hy]
  rfl

private theorem setIntegral_indicator_window {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    ∫ z in D, (window d₁ d₂ y).indicator (fun _ => (1 : ℂ)) (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F)
      = ((V.toReal * (Real.log (d₂ / d₁) / 2) : ℝ) : ℂ) := by
  have hpre : MeasurableSet {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂} :=
    (continuous_ideleNorm F).measurable (measurableSet_window d₁ d₂ y)
  have hlog : 0 ≤ Real.log (d₂ / d₁) / 2 :=
    div_nonneg (Real.log_nonneg ((one_le_div hd₁).mpr hd)) (by norm_num)
  have hfun : (fun z => (window d₁ d₂ y).indicator (fun _ => (1 : ℂ)) (ideleNorm F z))
      = {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂}.indicator (fun _ => (1 : ℂ)) := rfl
  rw [hfun, integral_indicator hpre, setIntegral_const, measureReal_def, Measure.restrict_apply hpre,
    measure_window hV hd₁ hd hy, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog, Complex.real_smul, mul_one]

end NormWindowVolume

end

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace SlabToTorus

variable {F : Type} [Field F] [NumberField F]

private theorem indicator_apply_coord_eq {S : Set (AdelicGL2 (𝓞 F) F)} {d₁ d₂ : ℝ}
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ}
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, t, k)) =
      (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)).indicator
        (fun _ => Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))) z := by
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, IwasawaBochner.iwasawaCoord]
  by_cases hz : NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k)
  · rw [if_pos ((hSco z t k).2 hz), if_pos hz]
    exact hcen z t k
  · rw [if_neg (fun h => hz ((hSco z t k).1 h)), if_neg hz]

private theorem measurable_indicator_mul_conj {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ} (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂) :
    Measurable (S.indicator fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) :=
  (hΦ₁m.mul (Complex.continuous_conj.measurable.comp hΦ₂m)).indicator hS

private theorem indicator_mul_conj_apply_mul {S : Set (AdelicGL2 (𝓞 F) F)}
    (hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (x * g) =
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) g := by
  classical
  intro x hx g
  simp only [Set.indicator_apply]
  by_cases hg : g ∈ S
  · rw [if_pos ((hSinv x hx g).2 hg), if_pos hg, hΦ₁inv x hx g, hΦ₂inv x hx g]
  · rw [if_neg (fun h => hg ((hSinv x hx g).1 h)), if_neg hg]

private theorem integrable_indicator_mul_conj_comp_iwasawaCoord
    [SFinite (NumberField.Idele.idelicHaar F)]
    {V : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ} (hY : ∀ t k, 0 < Y t k)
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))) :
    Integrable
      (fun p => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F p))
      (((NumberField.Idele.idelicHaar F).restrict D).prod
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
          (maximalCompactHaar F))) := by
  classical
  have hlog : 0 ≤ Real.log (d₂ / d₁) / 2 := div_nonneg (Real.log_nonneg ((one_le_div hd₁).2 hd)) zero_le_two
  have hpt := indicator_apply_coord_eq hSco Φ₁ Φ₂ hcen
  have hwin : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      (NumberField.Idele.idelicHaar F).restrict D
          (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)) =
        V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
    intro t k
    rw [Measure.restrict_apply (hnorm (NormWindowVolume.measurableSet_window d₁ d₂ _))]
    exact NormWindowVolume.measure_window hV hd₁ hd (hY t k)
  have hwinT : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      (NumberField.Idele.idelicHaar F).restrict D
          (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)) ≠ ∞ := by
    intro t k
    rw [hwin t k]
    exact ENNReal.mul_ne_top hVT ENNReal.ofReal_ne_top
  have hGm := measurable_indicator_mul_conj hS hΦ₁m hΦ₂m
  refine (integrable_prod_iff'
    (f := fun p => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F p))
    (hGm.comp hπ).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall fun y => ?_
    obtain ⟨t, k⟩ := y
    show Integrable (fun z => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g))
      (IwasawaBochner.iwasawaCoord F (z, t, k))) ((NumberField.Idele.idelicHaar F).restrict D)
    have hfun : (fun z => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g))
        (IwasawaBochner.iwasawaCoord F (z, t, k))) =
        (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)).indicator
          fun _ => Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))) :=
      funext fun z => hpt z t k
    have hIO : IntegrableOn
        (fun _ => Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
        (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k))
        ((NumberField.Idele.idelicHaar F).restrict D) :=
      integrableOn_const (hwinT t k)
    rw [hfun]
    exact hIO.integrable_indicator (hnorm (NormWindowVolume.measurableSet_window d₁ d₂ _))
  · show Integrable (fun y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      ∫ z, ‖S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, y))‖
        ∂((NumberField.Idele.idelicHaar F).restrict D))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))
    have hfun : (fun y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        ∫ z, ‖S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, y))‖
          ∂((NumberField.Idele.idelicHaar F).restrict D)) =
        fun y => (V.toReal * (Real.log (d₂ / d₁) / 2)) *
          ‖Φ₁ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)))‖ := by
      funext y
      obtain ⟨t, k⟩ := y
      simp_rw [hpt _ t k, norm_indicator_eq_indicator_norm]
      rw [integral_indicator_const _ (hnorm (NormWindowVolume.measurableSet_window d₁ d₂ _)),
        measureReal_def, hwin t k, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog, smul_eq_mul]
    rw [hfun]
    exact hint.norm.const_mul _

private theorem setIntegral_mul_conj_apply_out_eq_mul_setIntegral
    [SFinite (NumberField.Idele.idelicHaar F)]
    {cQ V : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hdis : IwasawaBochner.HasIwasawaDisintegration F cQ D D)
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S})
    (hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ} (hY : ∀ t k, 0 < Y t k)
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))) :
    ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ S},
        Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out) ∂(rationalTorusUnipotentQuotientMeasure F) =
      ((cQ.toReal * (V.toReal * (Real.log (d₂ / d₁) / 2)) : ℝ) : ℂ) *
        ∫ t in D, (NumberField.TateGlobal.ideleNorm F t)⁻¹ •
          ∫ k, Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  classical
  have hpt := indicator_apply_coord_eq hSco Φ₁ Φ₂ hcen
  have hGm := measurable_indicator_mul_conj hS hΦ₁m hΦ₂m
  have hGinv := indicator_mul_conj_apply_mul hSinv hΦ₁inv hΦ₂inv
  have hGπi := integrable_indicator_mul_conj_comp_iwasawaCoord hπ hnorm hV hVT hd₁ hd hS hY hSco Φ₁ Φ₂ hΦ₁m
    hΦ₂m hcen hint

  have hρ := IwasawaBochner.lintegral_out_eq_lintegral_smul_iwasawaMeasure hdis hπ hnorm
  have hptT : ∀ q : RationalTorusUnipotentQuotient F,
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S}.indicator
          (fun q => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out)) q =
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) q.out := by
    intro q
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← integral_indicator hT]
  simp_rw [hptT]
  rw [InvariantDescent.integral_apply_out_eq hρ _ hGm hGinv, integral_smul_measure]
  have hmap : ∫ g, S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) g
        ∂(IwasawaBochner.iwasawaMeasure F D D) =
      ∫ p, S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F p)
        ∂(((NumberField.Idele.idelicHaar F).restrict D).prod
          ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
            (maximalCompactHaar F))) := by
    unfold IwasawaBochner.iwasawaMeasure IteratedCoordinates.coordMeasure
    exact integral_map hπ.aemeasurable hGm.aestronglyMeasurable
  rw [hmap, integral_prod_symm _ hGπi]

  have hinner : ∀ y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F,
      ∫ z, S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, y))
          ∂((NumberField.Idele.idelicHaar F).restrict D) =
        ((V.toReal * (Real.log (d₂ / d₁) / 2) : ℝ) : ℂ) *
          (Φ₁ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)))) := by
    rintro ⟨t, k⟩
    have hpt' : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, t, k)) =
          (NormWindowVolume.window d₁ d₂ (Y t k)).indicator (fun _ => (1 : ℂ))
              (NumberField.TateGlobal.ideleNorm F z) *
            (Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
              starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))) := by
      intro z
      rw [hpt z t k]
      simp only [Set.indicator_apply, Set.mem_preimage]
      split_ifs <;> simp
    simp_rw [hpt']
    rw [integral_mul_const, NormWindowVolume.setIntegral_indicator_window hV hd₁ hd (hY t k)]
  simp_rw [hinner]
  rw [integral_const_mul, integral_prod _ hint,
    integral_withDensity_eq_integral_toReal_smul₀ (IwasawaBochner.measurable_torusWeight hnorm).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hw : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      (IwasawaBochner.torusWeight F t).toReal = (NumberField.TateGlobal.ideleNorm F t)⁻¹ := fun t =>
    ENNReal.toReal_ofReal (inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos (F := F) t).le)
  simp_rw [hw]
  rw [Complex.real_smul, ← mul_assoc]
  congr 1
  exact (Complex.ofReal_mul _ _).symm

private theorem integrableOn_mul_conj_apply_out
    [SFinite (NumberField.Idele.idelicHaar F)]
    {cQ V : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hdis : IwasawaBochner.HasIwasawaDisintegration F cQ D D) (hcQ : cQ ≠ ∞)
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S})
    (hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ} (hY : ∀ t k, 0 < Y t k)
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))) :
    IntegrableOn (fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out))
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S} (rationalTorusUnipotentQuotientMeasure F) := by
  classical
  have hGm := measurable_indicator_mul_conj hS hΦ₁m hΦ₂m
  have hGinv := indicator_mul_conj_apply_mul hSinv hΦ₁inv hΦ₂inv
  have hGπi := integrable_indicator_mul_conj_comp_iwasawaCoord hπ hnorm hV hVT hd₁ hd hS hY hSco Φ₁ Φ₂ hΦ₁m
    hΦ₂m hcen hint
  have hGi : Integrable (S.indicator fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g))
      (IwasawaBochner.iwasawaMeasure F D D) := by
    unfold IwasawaBochner.iwasawaMeasure IteratedCoordinates.coordMeasure
    exact (integrable_map_measure hGm.aestronglyMeasurable hπ.aemeasurable).2 hGπi
  have hout := IwasawaBochner.integrable_apply_out hdis hπ hnorm hcQ _ hGm hGinv hGi
  have hptT : ∀ q : RationalTorusUnipotentQuotient F,
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S}.indicator
          (fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out)) q =
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) q.out := by
    intro q
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← integrable_indicator_iff hT]
  rw [show ({q : RationalTorusUnipotentQuotient F | q.out ∈ S}.indicator
      fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out)) =
      fun q => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) q.out from funext hptT]
  exact hout

end SlabToTorus

end

end

section

open MeasureTheory NumberField NumberField.TateGlobal
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace IdeleClassPairing

variable {F : Type} [Field F] [NumberField F]

private scoped instance instSMulCommClassPrincipalIdeles :
    SMulCommClass (AdeleRing (𝓞 F) F)ˣ (M4aHerbrand.principalIdeles (𝓞 F) F) (AdeleRing (𝓞 F) F)ˣ :=
  ⟨fun a γ x =>
    show a * ((γ : (AdeleRing (𝓞 F) F)ˣ) * x) = (γ : (AdeleRing (𝓞 F) F)ˣ) * (a * x) from
      mul_left_comm _ _ _⟩

private theorem ideleNorm_eq_one_of_mem_principalIdeles {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) : ideleNorm F γ = 1 := by
  obtain ⟨η, rfl⟩ := MonoidHom.mem_range.mp hγ
  have h : distribHaarChar (AdeleRing (𝓞 F) F)
      ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) η) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap F η
  simp [ideleNorm, h]

private theorem apply_eq_one_of_mem_principalIdeles {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ) {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) : χ γ = 1 := by
  obtain ⟨η, rfl⟩ := MonoidHom.mem_range.mp hγ
  exact hχ η

private theorem conj_apply_of_isUnitaryChar {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχ : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    starRingEnd ℂ ((χ t : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ)⁻¹ := by
  have h1 : ‖((χ t : ℂˣ) : ℂ)‖ = 1 := hχ t
  have hmul : ((χ t : ℂˣ) : ℂ) * starRingEnd ℂ ((χ t : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    simp
  exact (inv_eq_of_mul_eq_one_right hmul).symm

private theorem setIntegral_eq_mul_setIntegral_of_ideleNorm_eq_one (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h₁ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ₁) (h₂ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ₂)
    {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (G : ℝ → ℂ) {t₀ : (AdeleRing (𝓞 F) F)ˣ} (ht₀ : ideleNorm F t₀ = 1) :
    ∫ t in D, ((χ₁ t : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t : ℂˣ) : ℂ) * G (ideleNorm F t)
        ∂(NumberField.Idele.idelicHaar F)
      = ((χ₁ t₀ : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t₀ : ℂˣ) : ℂ) *
        ∫ t in D, ((χ₁ t : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t : ℂˣ) : ℂ) * G (ideleNorm F t)
          ∂(NumberField.Idele.idelicHaar F) := by
  set Φ : (AdeleRing (𝓞 F) F)ˣ → ℂ :=
    fun t => ((χ₁ t : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t : ℂˣ) : ℂ) * G (ideleNorm F t) with hΦ

  have h1 : ∀ t, Φ (t * t₀) = ((χ₁ t₀ : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t₀ : ℂˣ) : ℂ) * Φ t := by
    intro t
    simp only [hΦ, map_mul, Units.val_mul, ideleNorm_mul, ht₀, mul_one]
    ring

  have h2 : ∫ t in D, Φ (t * t₀) ∂(NumberField.Idele.idelicHaar F)
      = ∫ y in t₀ • D, Φ y ∂(NumberField.Idele.idelicHaar F) := by
    have hpre : (fun t : (AdeleRing (𝓞 F) F)ˣ => t * t₀) ⁻¹' (t₀ • D) = D := by
      ext t
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      rw [mul_comm t, inv_mul_cancel_left]
    have h := (measurePreserving_mul_right (NumberField.Idele.idelicHaar F) t₀).setIntegral_preimage_emb
      (measurableEmbedding_mulRight t₀) Φ (t₀ • D)
    rw [hpre] at h
    exact h

  have hΦinv : ∀ (γ : M4aHerbrand.principalIdeles (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ), Φ (γ • t) = Φ t := by
    intro γ t
    simp only [hΦ, Subgroup.smul_def, smul_eq_mul, map_mul, ideleNorm_mul,
      apply_eq_one_of_mem_principalIdeles h₁ γ.2, apply_eq_one_of_mem_principalIdeles h₂ γ.2,
      ideleNorm_eq_one_of_mem_principalIdeles γ.2, one_mul]

  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.symm.toEquiv
  haveI : Countable Fˣ := Units.val_injective.countable
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 F) F) := by
    unfold M4aHerbrand.principalIdeles
    exact (MonoidHom.rangeRestrict_surjective _).countable
  have h3 : ∫ y in t₀ • D, Φ y ∂(NumberField.Idele.idelicHaar F)
      = ∫ t in D, Φ t ∂(NumberField.Idele.idelicHaar F) :=
    (hD.smul_of_comm t₀).setIntegral_eq hD hΦinv
  calc ∫ t in D, Φ t ∂(NumberField.Idele.idelicHaar F)
      = ∫ y in t₀ • D, Φ y ∂(NumberField.Idele.idelicHaar F) := h3.symm
    _ = ∫ t in D, Φ (t * t₀) ∂(NumberField.Idele.idelicHaar F) := h2.symm
    _ = ∫ t in D, ((χ₁ t₀ : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t₀ : ℂˣ) : ℂ) * Φ t
          ∂(NumberField.Idele.idelicHaar F) := integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ((χ₁ t₀ : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t₀ : ℂˣ) : ℂ) * ∫ t in D, Φ t
          ∂(NumberField.Idele.idelicHaar F) := integral_const_mul _ _

private theorem setIntegral_eq_zero_of_apply_ne (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h₁ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ₁) (h₂ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ₂)
    (h₂u : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ₂)
    {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (G : ℝ → ℂ) {t₀ : (AdeleRing (𝓞 F) F)ˣ} (ht₀ : t₀ ∈ normOneIdeles F) (hne : χ₁ t₀ ≠ χ₂ t₀) :
    ∫ t in D, ((χ₁ t : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t : ℂˣ) : ℂ) * G (ideleNorm F t)
        ∂(NumberField.Idele.idelicHaar F) = 0 := by
  have h := setIntegral_eq_mul_setIntegral_of_ideleNorm_eq_one χ₁ χ₂ h₁ h₂ hD G
    ((mem_normOneIdeles_iff t₀).mp ht₀)

  have hlam : ((χ₁ t₀ : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t₀ : ℂˣ) : ℂ) ≠ 1 := by
    rw [conj_apply_of_isUnitaryChar h₂u t₀]
    intro hone
    apply hne
    have hne0 : ((χ₂ t₀ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have heq : ((χ₁ t₀ : ℂˣ) : ℂ) = ((χ₂ t₀ : ℂˣ) : ℂ) := by
      have := congrArg (fun w => w * ((χ₂ t₀ : ℂˣ) : ℂ)) hone
      simpa [mul_assoc, inv_mul_cancel₀ hne0] using this
    exact Units.val_injective heq
  have hsub : (1 - ((χ₁ t₀ : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t₀ : ℂˣ) : ℂ)) *
      ∫ t in D, ((χ₁ t : ℂˣ) : ℂ) * starRingEnd ℂ ((χ₂ t : ℂˣ) : ℂ) * G (ideleNorm F t)
        ∂(NumberField.Idele.idelicHaar F) = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (Ne.symm hlam))

private theorem exists_apply_ne_fst (μ₁ ν₁ μ₂ ν₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hprod : ∀ x ∈ normOneIdeles F, μ₁ x * ν₁ x = μ₂ x * ν₂ x)
    (hdist : ∃ x ∈ normOneIdeles F, μ₁ x ≠ μ₂ x ∨ ν₁ x ≠ ν₂ x) :
    ∃ x ∈ normOneIdeles F, μ₁ x ≠ μ₂ x := by
  obtain ⟨x, hx, h⟩ := hdist
  refine ⟨x, hx, ?_⟩
  rcases h with h | h
  · exact h
  · intro hμ
    apply h
    have := hprod x hx
    rw [hμ] at this
    exact mul_left_cancel this

private theorem exists_apply_ne_snd (μ₁ ν₁ μ₂ ν₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hprod : ∀ x ∈ normOneIdeles F, μ₁ x * ν₁ x = μ₂ x * ν₂ x)
    (hdist : ∃ x ∈ normOneIdeles F, μ₁ x ≠ μ₂ x ∨ ν₁ x ≠ ν₂ x) :
    ∃ x ∈ normOneIdeles F, ν₁ x ≠ ν₂ x := by
  obtain ⟨x, hx, h⟩ := hdist
  refine ⟨x, hx, ?_⟩
  rcases h with h | h
  · intro hν
    apply h
    have := hprod x hx
    rw [hν] at this
    exact mul_right_cancel this
  · exact h

end IdeleClassPairing
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace NormDisintegration

variable {F : Type} [Field F] [NumberField F]

private theorem map_ideleNorm_restrict_eq {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹) :
    ((NumberField.Idele.idelicHaar F).restrict D).map (ideleNorm F)
      = V • ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun y => ENNReal.ofReal y⁻¹) := by
  classical
  have hmeas : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  ext s hs
  have h1 : ((NumberField.Idele.idelicHaar F).restrict D).map (ideleNorm F) s
      = ∫⁻ z in D, s.indicator 1 (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) := by
    rw [Measure.map_apply hmeas hs, ← lintegral_indicator_one (hmeas hs)]
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  have h2 : (V • ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun y => ENNReal.ofReal y⁻¹)) s
      = V * ∫⁻ y in Set.Ioi (0 : ℝ), s.indicator 1 y * ENNReal.ofReal y⁻¹ := by
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs, ← lintegral_indicator hs]
    congr 1
    refine lintegral_congr (fun y => ?_)
    simp only [Set.indicator_apply, Pi.one_apply]
    split_ifs <;> simp
  rw [h1, hV _ (measurable_one.indicator hs), h2]

private theorem setIntegral_comp_ideleNorm_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (G : ℝ → E) (hG : AEStronglyMeasurable G (volume.restrict (Set.Ioi (0 : ℝ)))) :
    ∫ z in D, G (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F)
      = V.toReal • ∫ y in Set.Ioi (0 : ℝ), y⁻¹ • G y := by
  have hmeas : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  have hmap := map_ideleNorm_restrict_eq hV
  have hG' : AEStronglyMeasurable G (((NumberField.Idele.idelicHaar F).restrict D).map (ideleNorm F)) := by
    rw [hmap]
    exact (hG.mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure V
  have hdens : Measurable fun y : ℝ => ENNReal.ofReal y⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
  rw [← integral_map hmeas.aemeasurable hG', hmap, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (le_of_lt hy))]

private theorem setIntegral_comp_ideleNorm_eq_mul {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (G : ℝ → ℂ) (hG : AEStronglyMeasurable G (volume.restrict (Set.Ioi (0 : ℝ)))) :
    ∫ z in D, G (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F)
      = (V.toReal : ℂ) * ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * G y := by
  simp only [setIntegral_comp_ideleNorm_eq hV G hG, Complex.real_smul]

end NormDisintegration
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace NormDisintegration

variable {F : Type} [Field F] [NumberField F]

private theorem map_prodMap_ideleNorm_restrict_prod_eq (hnorm : Measurable (ideleNorm F))
    [SFinite (NumberField.Idele.idelicHaar F)] {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {K : Type*} [MeasurableSpace K] (m : Measure K) [SFinite m] :
    (((NumberField.Idele.idelicHaar F).restrict D).prod m).map (Prod.map (ideleNorm F) id) =
      V • (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun y => ENNReal.ofReal y⁻¹).prod m) := by
  rw [← Measure.map_prod_map _ _ hnorm measurable_id, map_ideleNorm_restrict_eq hV, Measure.map_id,
    Measure.prod_smul_left]

private theorem integrable_withDensity_prod_of_norm_le (hnorm : Measurable (ideleNorm F))
    [SFinite (NumberField.Idele.idelicHaar F)] {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) {K : Type*} [MeasurableSpace K] (m : Measure K) [SFinite m]
    {H : (AdeleRing (𝓞 F) F)ˣ × K → ℂ}
    (hHm : AEStronglyMeasurable H (((NumberField.Idele.idelicHaar F).restrict D).prod m))
    {G₀ : ℝ × K → ℝ} (hG₀m : Measurable G₀) (hle : ∀ t k, ‖H (t, k)‖ ≤ G₀ (ideleNorm F t, k))
    (hG : Integrable (fun p : ℝ × K => p.1⁻¹ * (p.1⁻¹ * G₀ p)) ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    Integrable H ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
      fun t => ENNReal.ofReal (ideleNorm F t)⁻¹).prod m) := by

  have hG₁ : Integrable (fun q : ℝ × K => q.1⁻¹ * G₀ q)
      ((((NumberField.Idele.idelicHaar F).restrict D).prod m).map (Prod.map (ideleNorm F) id)) := by
    rw [map_prodMap_ideleNorm_restrict_prod_eq hnorm hV m]
    refine Integrable.smul_measure ?_ hVT
    rw [prod_withDensity_left (measurable_inv.ennreal_ofReal),
      integrable_withDensity_iff_integrable_smul' (measurable_fst.fun_inv.ennreal_ofReal)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hG.norm.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact ((measurable_fst.fun_inv.ennreal_ofReal.ennreal_toReal).smul
        (measurable_fst.inv.mul hG₀m)).aestronglyMeasurable
    · rw [norm_smul, norm_mul (q.1⁻¹) (q.1⁻¹ * G₀ q)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, ENNReal.toReal_ofReal', abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)

  have hG₂ : Integrable (fun p : (AdeleRing (𝓞 F) F)ˣ × K => (ideleNorm F p.1)⁻¹ * G₀ (ideleNorm F p.1, p.2))
      (((NumberField.Idele.idelicHaar F).restrict D).prod m) :=
    (integrable_map_measure hG₁.aestronglyMeasurable (hnorm.prodMap measurable_id).aemeasurable).1 hG₁

  rw [prod_withDensity_left (hnorm.fun_inv.ennreal_ofReal),
    integrable_withDensity_iff_integrable_smul'
      (f := fun z : (AdeleRing (𝓞 F) F)ˣ × K => ENNReal.ofReal (ideleNorm F z.1)⁻¹)
      ((hnorm.comp measurable_fst).fun_inv.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine hG₂.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hnorm.comp measurable_fst).fun_inv.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable.smul hHm
  · have h0 : 0 ≤ (ideleNorm F p.1)⁻¹ := inv_nonneg.2 (ideleNorm_pos (F := F) p.1).le
    rw [norm_smul, Real.norm_eq_abs, ENNReal.toReal_ofReal h0, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hle p.1 p.2) h0

end NormDisintegration
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

noncomputable section

open MeasureTheory Real

namespace MellinParseval

variable {C : Type*} [MeasurableSpace C] {μ : Measure C} [SFinite μ]

private theorem rpow_neg_neg_add_self_div (σ y : ℝ) : y ^ (-(-σ + σ)) / y = y⁻¹ := by
  rw [neg_add_cancel, neg_zero, Real.rpow_zero, one_div]

private theorem setIntegral_inv_mul_lineProfile_mul_conj_lineProfile (σ : ℝ) {a b : ℝ → ℂ}
    (ha : Integrable a) (hac : Continuous a) (hap : HasIntegrableProfile σ a) (hb : Integrable b) :
    ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) *
        (lineProfile σ a y * starRingEnd ℂ (lineProfile (-σ) b y))
      = ((2 * π : ℝ) : ℂ) * ∫ t : ℝ, a t * starRingEnd ℂ (b t) := by
  have h := integral_conj_lineProfile_mul_lineProfile (-σ) σ hb ha hac hap
  have hL : (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) *
        (lineProfile σ a y * starRingEnd ℂ (lineProfile (-σ) b y)))
      = fun y : ℝ => ((y ^ (-(-σ + σ)) / y : ℝ) : ℂ) *
        (starRingEnd ℂ (lineProfile (-σ) b y) * lineProfile σ a y) := by
    funext y
    rw [rpow_neg_neg_add_self_div]
    ring
  have hR : (fun t : ℝ => a t * starRingEnd ℂ (b t)) = fun t : ℝ => starRingEnd ℂ (b t) * a t := by
    funext t
    ring
  rw [hL, hR]
  exact h

private theorem integrableOn_inv_mul_lineProfile_mul_conj_lineProfile (σ : ℝ) {a b : ℝ → ℂ}
    (hap : HasIntegrableProfile σ a) (hb : Integrable b) :
    IntegrableOn (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) *
        (lineProfile σ a y * starRingEnd ℂ (lineProfile (-σ) b y))) (Set.Ioi 0) := by
  have h := integrableOn_conj_lineProfile_mul_lineProfile (-σ) σ hb hap
  have hL : (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) *
        (lineProfile σ a y * starRingEnd ℂ (lineProfile (-σ) b y)))
      = fun y : ℝ => ((y ^ (-(-σ + σ)) / y : ℝ) : ℂ) *
        (starRingEnd ℂ (lineProfile (-σ) b y) * lineProfile σ a y) := by
    funext y
    rw [rpow_neg_neg_add_self_div]
    ring
  rw [hL]
  exact h

private theorem setIntegral_inv_mul_integral_lineProfile_mul_conj_lineProfile (σ : ℝ) (a b : C → ℝ → ℂ)
    (ha : ∀ c, Integrable (a c)) (hac : ∀ c, Continuous (a c))
    (hap : ∀ c, HasIntegrableProfile σ (a c)) (hb : ∀ c, Integrable (b c))
    (hL : Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b p.2) p.1)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hint : Integrable (fun p : ℝ × C => a p.2 p.1 * starRingEnd ℂ (b p.2 p.1)) (volume.prod μ)) :
    ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) *
        ∫ c, lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y) ∂μ
      = ((2 * π : ℝ) : ℂ) * ∫ t : ℝ, ∫ c, a c t * starRingEnd ℂ (b c t) ∂μ := by
  have hL' : Integrable (Function.uncurry fun (y : ℝ) (c : C) => ((y⁻¹ : ℝ) : ℂ) *
      (lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ) := hL
  have hint' : Integrable (Function.uncurry fun (t : ℝ) (c : C) => a c t * starRingEnd ℂ (b c t))
      (volume.prod μ) := hint

  have h1 : ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) *
        ∫ c, lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y) ∂μ
      = ∫ y in Set.Ioi (0 : ℝ), ∫ c, ((y⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y)) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    exact (integral_const_mul _ _).symm

  have h3 : ∀ c, ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y))
      = ((2 * π : ℝ) : ℂ) * ∫ t : ℝ, a c t * starRingEnd ℂ (b c t) :=
    fun c => setIntegral_inv_mul_lineProfile_mul_conj_lineProfile σ (ha c) (hac c) (hap c) (hb c)
  calc ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) *
          ∫ c, lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y) ∂μ
      = ∫ y in Set.Ioi (0 : ℝ), ∫ c, ((y⁻¹ : ℝ) : ℂ) *
          (lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y)) ∂μ := h1
    _ = ∫ c, (∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) *
          (lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y))) ∂μ :=
        integral_integral_swap hL'
    _ = ∫ c, (((2 * π : ℝ) : ℂ) * ∫ t : ℝ, a c t * starRingEnd ℂ (b c t)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall h3)
    _ = ((2 * π : ℝ) : ℂ) * ∫ c, (∫ t : ℝ, a c t * starRingEnd ℂ (b c t)) ∂μ := integral_const_mul _ _
    _ = ((2 * π : ℝ) : ℂ) * ∫ t : ℝ, ∫ c, a c t * starRingEnd ℂ (b c t) ∂μ := by
        rw [integral_integral_swap hint']

end MellinParseval
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField NumberField.TateGlobal MellinParseval
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace TorusPairing

variable {F : Type} [Field F] [NumberField F]

private theorem ofReal_cpow_half_mul_conj {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (1 / 2 : ℂ) * starRingEnd ℂ ((y : ℂ) ^ (1 / 2 : ℂ)) = (y : ℂ) := by
  have h : (y : ℂ) ^ (1 / 2 : ℂ) = (y : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h, ← Complex.ofReal_cpow hy.le, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.rpow_add hy]
  norm_num

section Compact

variable {C : Type*} [MeasurableSpace C] {m : Measure C}

private def pairInt (σ : ℝ) (a b : C → ℝ → ℂ) (m : Measure C) (y : ℝ) : ℂ :=
  ∫ c, lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y) ∂m

private theorem ae_integrable_pairInt_integrand (σ : ℝ) [SFinite m] {a b : C → ℝ → ℂ}
    (hL : Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    ∀ᵐ y ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun c => lineProfile σ (a c) y * starRingEnd ℂ (lineProfile (-σ) (b c) y)) m := by
  filter_upwards [hL.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with y hy hypos
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hypos).ne'
  refine (hy.const_mul (y : ℂ)).congr (Filter.Eventually.of_forall fun c => ?_)
  simp only [Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ hy0, one_mul]

variable [SFinite m]

private theorem integrable_inv_mul_pairInt (σ : ℝ) {a b : C → ℝ → ℂ}
    (hL : Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    Integrable (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) * pairInt σ a b m y) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine hL.integral_prod_left.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [pairInt, integral_const_mul]

private theorem aestronglyMeasurable_pairInt (σ : ℝ) {a b : C → ℝ → ℂ}
    (hL : Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    AEStronglyMeasurable (pairInt σ a b m) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable (fun y : ℝ => (y : ℂ) * (((y⁻¹ : ℝ) : ℂ) * pairInt σ a b m y))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Complex.continuous_ofReal.aestronglyMeasurable.mul (integrable_inv_mul_pairInt σ hL).aestronglyMeasurable
  refine h1.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hy).ne'
  simp only [Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ hy0, one_mul]

end Compact
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section Pointwise

variable {C : Type*}

private theorem mul_conj_eq_sum {ι : Type} [Fintype ι] (μ : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (σ : ℝ)
    (a b : ι → C → ℝ → ℂ) {P Q : (AdeleRing (𝓞 F) F)ˣ → C → ℂ}
    (hP : ∀ t c, P t c = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      lineProfile σ (a e c) (ideleNorm F t))
    (hQ : ∀ t c, Q t c = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      lineProfile (-σ) (b e c) (ideleNorm F t))
    (t : (AdeleRing (𝓞 F) F)ˣ) (c : C) :
    P t c * starRingEnd ℂ (Q t c)
      = ∑ e, ∑ e', (((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ)) *
          (lineProfile σ (a e c) (ideleNorm F t) * starRingEnd ℂ (lineProfile (-σ) (b e' c) (ideleNorm F t))) := by
  rw [hP, hQ, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  have hpow := ofReal_cpow_half_mul_conj (ideleNorm_pos t)
  simp only [map_mul]
  linear_combination (((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) *
    (lineProfile σ (a e c) (ideleNorm F t) * starRingEnd ℂ (lineProfile (-σ) (b e' c) (ideleNorm F t)))) * hpow

end Pointwise
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section Ideles

variable {C : Type*} [MeasurableSpace C] {m : Measure C}

private theorem ae_integrable_pairInt_integrand_ideleNorm {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {ι : Type} [Fintype ι] [SFinite m] (σ : ℝ) {a b : ι → C → ℝ → ℂ}
    (hL : ∀ e e', Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a e p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b e' p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    ∀ᵐ t ∂((NumberField.Idele.idelicHaar F).restrict D), ∀ e e',
      Integrable (fun c => lineProfile σ (a e c) (ideleNorm F t) *
        starRingEnd ℂ (lineProfile (-σ) (b e' c) (ideleNorm F t))) m := by
  have hmeas : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  have hmap := NormDisintegration.map_ideleNorm_restrict_eq hV
  have h0 : ∀ᵐ y ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ e e',
      Integrable (fun c => lineProfile σ (a e c) y * starRingEnd ℂ (lineProfile (-σ) (b e' c) y)) m :=
    ae_all_iff.2 fun e => ae_all_iff.2 fun e' => ae_integrable_pairInt_integrand σ (hL e e')
  have h1 : ∀ᵐ y ∂(((NumberField.Idele.idelicHaar F).restrict D).map (ideleNorm F)), ∀ e e',
      Integrable (fun c => lineProfile σ (a e c) y * starRingEnd ℂ (lineProfile (-σ) (b e' c) y)) m := by
    rw [hmap]
    exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le h0) V
  exact ae_of_ae_map hmeas.aemeasurable h1

variable [SFinite m]

private theorem integrable_pairInt_comp_ideleNorm {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (σ : ℝ) {a b : C → ℝ → ℂ}
    (hL : Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    Integrable (fun t => pairInt σ a b m (ideleNorm F t)) ((NumberField.Idele.idelicHaar F).restrict D) := by
  have hmeas : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  have hmap := NormDisintegration.map_ideleNorm_restrict_eq hV
  have hG := aestronglyMeasurable_pairInt σ hL
  have hG' : AEStronglyMeasurable (pairInt σ a b m)
      (((NumberField.Idele.idelicHaar F).restrict D).map (ideleNorm F)) := by
    rw [hmap]
    exact (hG.mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure V
  have hdens : Measurable fun y : ℝ => Real.toNNReal y⁻¹ := measurable_real_toNNReal.comp measurable_inv
  have hint : Integrable (pairInt σ a b m) (((NumberField.Idele.idelicHaar F).restrict D).map (ideleNorm F)) := by
    rw [hmap]
    refine Integrable.smul_measure ?_ hVT
    rw [show (fun y : ℝ => ENNReal.ofReal y⁻¹) = fun y : ℝ => ((Real.toNNReal y⁻¹ : ℝ≥0) : ℝ≥0∞) from rfl,
      integrable_withDensity_iff_integrable_smul₀ hdens.aemeasurable]
    refine (integrable_inv_mul_pairInt σ hL).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr (Set.mem_Ioi.mp hy).le), Complex.real_smul]
  exact (integrable_map_measure hG' hmeas.aemeasurable).mp hint

private theorem setIntegral_inv_smul_integral_mul_conj_eq_mul_sum {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞)
    {ι : Type} [Fintype ι] (μ : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (hμu : ∀ e, AutomorphicForm.IsUnitaryChar (𝓞 F) F (μ e))
    (hμic : ∀ e, AutomorphicForm.IsIdeleClassChar (𝓞 F) F (μ e))
    (hμm : ∀ e, Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ((μ e t : ℂˣ) : ℂ))
    (hdist : ∀ e e', e ≠ e' → ∃ x ∈ normOneIdeles F, μ e x ≠ μ e' x)
    (σ : ℝ) (a b : ι → C → ℝ → ℂ)
    (ha : ∀ e c, Integrable (a e c)) (hac : ∀ e c, Continuous (a e c))
    (hap : ∀ e c, HasIntegrableProfile σ (a e c)) (hb : ∀ e c, Integrable (b e c))
    (hL : ∀ e e', Integrable (fun p : ℝ × C => ((p.1⁻¹ : ℝ) : ℂ) *
        (lineProfile σ (a e p.2) p.1 * starRingEnd ℂ (lineProfile (-σ) (b e' p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m))
    (hint : ∀ e, Integrable (fun p : ℝ × C => a e p.2 p.1 * starRingEnd ℂ (b e p.2 p.1)) (volume.prod m))
    (P Q : (AdeleRing (𝓞 F) F)ˣ → C → ℂ)
    (hP : ∀ t c, P t c = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      lineProfile σ (a e c) (ideleNorm F t))
    (hQ : ∀ t c, Q t c = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      lineProfile (-σ) (b e c) (ideleNorm F t)) :
    ∫ t in D, (ideleNorm F t)⁻¹ • ∫ c, P t c * starRingEnd ℂ (Q t c) ∂m ∂(NumberField.Idele.idelicHaar F)
      = ((V.toReal * (2 * Real.pi) : ℝ) : ℂ) * ∑ e, ∫ τ : ℝ, ∫ c, a e c τ * starRingEnd ℂ (b e c τ) ∂m := by

  set T : ι → ι → (AdeleRing (𝓞 F) F)ˣ → ℂ := fun e e' t =>
    ((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) * pairInt σ (a e) (b e') m (ideleNorm F t) with hT

  have hexp : ∀ᵐ t ∂((NumberField.Idele.idelicHaar F).restrict D),
      (ideleNorm F t)⁻¹ • (∫ c, P t c * starRingEnd ℂ (Q t c) ∂m) = ∑ e, ∑ e', T e e' t := by
    filter_upwards [ae_integrable_pairInt_integrand_ideleNorm hV σ hL] with t hgood
    have hy : ((ideleNorm F t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos t).ne'
    have hy1 : ((ideleNorm F t : ℝ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hy
    have hfun : (fun c => P t c * starRingEnd ℂ (Q t c)) = fun c => ∑ e, ∑ e',
        (((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ)) *
          (lineProfile σ (a e c) (ideleNorm F t) * starRingEnd ℂ (lineProfile (-σ) (b e' c) (ideleNorm F t))) :=
      funext fun c => mul_conj_eq_sum μ σ a b hP hQ t c
    rw [hfun, integral_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ => (hgood e e').const_mul
      (((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ)),
      Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_finsetSum _ fun e' _ => (hgood e e').const_mul
      (((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [integral_const_mul]
    simp only [hT, pairInt, Complex.ofReal_inv]
    linear_combination (((μ e t : ℂˣ) : ℂ) * starRingEnd ℂ ((μ e' t : ℂˣ) : ℂ) *
      ∫ c, lineProfile σ (a e c) (ideleNorm F t) * starRingEnd ℂ (lineProfile (-σ) (b e' c) (ideleNorm F t)) ∂m) * hy1

  have hTint : ∀ e e', Integrable (T e e') ((NumberField.Idele.idelicHaar F).restrict D) := by
    intro e e'
    have hG := integrable_pairInt_comp_ideleNorm hV hVT σ (hL e e')
    refine hG.norm.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact ((hμm e).aestronglyMeasurable.mul
        (Complex.continuous_conj.measurable.comp (hμm e')).aestronglyMeasurable).mul hG.aestronglyMeasurable
    · simp only [hT, norm_mul, Complex.norm_conj, hμu e t, hμu e' t, one_mul, le_refl]

  rw [integral_congr_ae hexp, integral_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ => hTint e e',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum _ fun e' _ => hTint e e',
    Finset.sum_eq_single e (fun e' _ hne => ?_) (fun h => absurd (Finset.mem_univ e) h)]
  ·
    have hdiag : ∫ t in D, T e e t ∂(NumberField.Idele.idelicHaar F)
        = ∫ t in D, pairInt σ (a e) (b e) m (ideleNorm F t) ∂(NumberField.Idele.idelicHaar F) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hT]
      rw [IdeleClassPairing.conj_apply_of_isUnitaryChar (hμu e) t, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    rw [hdiag, NormDisintegration.setIntegral_comp_ideleNorm_eq_mul hV _ (aestronglyMeasurable_pairInt σ (hL e e))]
    have h7 := MellinParseval.setIntegral_inv_mul_integral_lineProfile_mul_conj_lineProfile σ (a e) (b e) (ha e)
      (hac e) (hap e) (hb e) (hL e e) (hint e)
    simp only [pairInt]
    rw [h7]
    push_cast
    ring
  ·
    obtain ⟨x, hx, hne'⟩ := hdist e e' (Ne.symm hne)
    simp only [hT]
    exact IdeleClassPairing.setIntegral_eq_zero_of_apply_ne (μ e) (μ e') (hμic e) (hμic e') (hμu e') hDF
      (pairInt σ (a e) (b e') m) hx hne'

end Ideles
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end TorusPairing
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

noncomputable section

open MeasureTheory

namespace MellinParseval

private theorem integral_mul_cpow_add_half_mul (σ : ℝ) (a : ℝ → ℂ) (c : ℂ) {y : ℝ} (hy : 0 < y) :
    ∫ τ : ℝ, c * (y : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I + 1 / 2) * a τ
      = c * (y : ℂ) ^ (1 / 2 : ℂ) * lineProfile σ a y := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpt : ∀ τ : ℝ, c * (y : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I + 1 / 2) * a τ
      = (c * (y : ℂ) ^ (1 / 2 : ℂ)) * ((y : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I) * a τ) := by
    intro τ
    rw [Complex.cpow_add _ _ hy0]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  simp only [lineProfile, smul_eq_mul, mul_assoc]

private theorem integral_mul_cpow_add_half_mul' (σ : ℝ) (a val : ℝ → ℂ) (c : ℂ) {y : ℝ} (hy : 0 < y)
    (h : ∀ τ : ℝ, val τ = c * (y : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I + 1 / 2) * a τ) :
    ∫ τ : ℝ, val τ = c * (y : ℂ) ^ (1 / 2 : ℂ) * lineProfile σ a y := by
  rw [show val = fun τ : ℝ => c * (y : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I + 1 / 2) * a τ from
    funext h]
  exact integral_mul_cpow_add_half_mul σ a c hy

end MellinParseval
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open NumberField NumberField.AdelicLevel
open AutomorphicForm
open scoped ComplexConjugate

noncomputable section

namespace IwasawaSectionValues

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem diagOne_mem_adelicBorel (t : (AdeleRing R K)ˣ) : diagOne t ∈ adelicBorel R K := by
  show ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  have hval : ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.diagonal ![(t : AdeleRing R K), 1] := rfl
  rw [hval]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem borelDiagFst_diagOne (t : (AdeleRing R K)ˣ) (hmem : diagOne t ∈ adelicBorel R K) :
    borelDiagFst (⟨diagOne t, hmem⟩ : ↥(adelicBorel R K)) = t := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0 = (t : AdeleRing R K)
  have hval : ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.diagonal ![(t : AdeleRing R K), 1] := rfl
  rw [hval, Matrix.diagonal_apply_eq]
  rfl

private theorem borelDiagSnd_diagOne (t : (AdeleRing R K)ˣ) (hmem : diagOne t ∈ adelicBorel R K) :
    borelDiagSnd (⟨diagOne t, hmem⟩ : ↥(adelicBorel R K)) = 1 := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1 = (1 : AdeleRing R K)
  have hval : ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.diagonal ![(t : AdeleRing R K), 1] := rfl
  rw [hval, Matrix.diagonal_apply_eq]
  rfl

section Values

variable {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ} {φ : AdelicGL2 R K → ℂ}

private theorem apply_diagOne_mul (hφ : IsInducedSection R K χ₁ χ₂ φ) (t : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    φ (diagOne t * g) = ((χ₁ t : ℂˣ) : ℂ) * φ g := by
  rw [hφ (diagOne t) (diagOne_mem_adelicBorel t) g, borelDiagFst_diagOne, borelDiagSnd_diagOne, map_one,
    Units.val_one, mul_one]

private theorem
apply_centralScalar_mul (hφ : IsInducedSection R K χ₁ χ₂ φ) (z : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    φ (centralScalar R K z * g) = ((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  rw [hφ (centralScalar R K z) (centralScalar_mem_adelicBorel R K z) g, borelDiagFst_centralScalar,
    borelDiagSnd_centralScalar]

end Values
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section Eta

variable {μ ν : (AdeleRing R K)ˣ →* ℂˣ} {α : (AdeleRing R K)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {s : ℂ}
  {φ : AdelicGL2 R K → ℂ}

private theorem eta_apply_diagOne_mul (hφ : IsInducedSection R K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (t : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    φ (diagOne t * g) = ((μ t : ℂˣ) : ℂ) * ((((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)) * φ g := by
  rw [apply_diagOne_mul hφ, etaFst_apply, Units.val_mul, cpowChar_apply_val]

private theorem eta_apply_centralScalar_mul (hφ : IsInducedSection R K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (z : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    φ (centralScalar R K z * g) = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * φ g := by
  rw [apply_centralScalar_mul hφ, ← Units.val_mul, etaFst_mul_etaSnd, Units.val_mul]

private theorem
eta_apply_centralScalar_mul_diagOne_mul (hφ : IsInducedSection R K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (z t : (AdeleRing R K)ˣ) (k : AdelicGL2 R K) :
    φ (centralScalar R K z * diagOne t * k)
      = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((μ t : ℂˣ) : ℂ) * ((((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)) * φ k := by
  rw [mul_assoc, eta_apply_centralScalar_mul hφ, eta_apply_diagOne_mul hφ]
  ring

end Eta
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

private theorem conj_ofReal_cpow {a : ℝ} (ha : 0 < a) (w : ℂ) : conj ((a : ℂ) ^ w) = (a : ℂ) ^ (conj w) := by
  have harg : (a : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha.le]
    exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

private theorem ofReal_cpow_mul_conj_ofReal_cpow {a : ℝ} (ha : 0 < a) (σ τ τ' : ℝ) :
    (a : ℂ) ^ (((σ : ℂ) + (τ : ℂ) * Complex.I) + 1 / 2) * conj ((a : ℂ) ^ ((-(σ : ℂ) + (τ' : ℂ) * Complex.I) + 1 / 2))
      = (a : ℂ) ^ (((τ - τ' : ℝ) : ℂ) * Complex.I) * (a : ℂ) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  rw [conj_ofReal_cpow ha, ← Complex.cpow_add _ _ ha0]
  have hexp : ((σ : ℂ) + (τ : ℂ) * Complex.I) + 1 / 2 + conj ((-(σ : ℂ) + (τ' : ℂ) * Complex.I) + 1 / 2)
      = ((τ - τ' : ℝ) : ℂ) * Complex.I + 1 := by
    apply Complex.ext <;> simp <;> ring
  rw [hexp, Complex.cpow_add _ _ ha0, Complex.cpow_one]

section Pair

variable {μ₁ ν₁ μ₂ ν₂ : (AdeleRing R K)ˣ →* ℂˣ} {α : (AdeleRing R K)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)}
  {φ ψ : AdelicGL2 R K → ℂ}

private theorem _root_.IwasawaSectionValues.mul_conj_apply_iwasawa {s s' : ℂ} (hφ : IsInducedSection R K (etaFst μ₁ α hα s) (etaSnd ν₁ α hα s) φ)
    (hψ : IsInducedSection R K (etaFst μ₂ α hα s') (etaSnd ν₂ α hα s') ψ) (z t : (AdeleRing R K)ˣ)
    (k : AdelicGL2 R K) :
    φ (centralScalar R K z * diagOne t * k) * conj (ψ (centralScalar R K z * diagOne t * k))
      = (((μ₁ z : ℂˣ) : ℂ) * ((ν₁ z : ℂˣ) : ℂ) * ((μ₁ t : ℂˣ) : ℂ)
            * conj (((μ₂ z : ℂˣ) : ℂ) * ((ν₂ z : ℂˣ) : ℂ) * ((μ₂ t : ℂˣ) : ℂ)))
          * ((((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * conj ((((α t : ℝˣ) : ℝ) : ℂ) ^ (s' + 1 / 2)))
          * (φ k * conj (ψ k)) := by
  rw [eta_apply_centralScalar_mul_diagOne_mul hφ, eta_apply_centralScalar_mul_diagOne_mul hψ]
  simp only [map_mul]
  ring

p2m_export "IwasawaSectionValues" "mul_conj_apply_iwasawa"

private theorem mul_conj_apply_iwasawa_of_lines (σ τ τ' : ℝ)
    (hφ : IsInducedSection R K (etaFst μ₁ α hα ((σ : ℂ) + (τ : ℂ) * Complex.I))
      (etaSnd ν₁ α hα ((σ : ℂ) + (τ : ℂ) * Complex.I)) φ)
    (hψ : IsInducedSection R K (etaFst μ₂ α hα (-(σ : ℂ) + (τ' : ℂ) * Complex.I))
      (etaSnd ν₂ α hα (-(σ : ℂ) + (τ' : ℂ) * Complex.I)) ψ) (z t : (AdeleRing R K)ˣ) (k : AdelicGL2 R K) :
    φ (centralScalar R K z * diagOne t * k) * conj (ψ (centralScalar R K z * diagOne t * k))
      = (((μ₁ z : ℂˣ) : ℂ) * ((ν₁ z : ℂˣ) : ℂ) * ((μ₁ t : ℂˣ) : ℂ)
            * conj (((μ₂ z : ℂˣ) : ℂ) * ((ν₂ z : ℂˣ) : ℂ) * ((μ₂ t : ℂˣ) : ℂ)))
          * ((((α t : ℝˣ) : ℝ) : ℂ) ^ (((τ - τ' : ℝ) : ℂ) * Complex.I) * (((α t : ℝˣ) : ℝ) : ℂ))
          * (φ k * conj (ψ k)) := by
  rw [mul_conj_apply_iwasawa hφ hψ, ofReal_cpow_mul_conj_ofReal_cpow (hα t) σ τ τ']

end Pair
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end IwasawaSectionValues
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace TorusExpansion

variable {F : Type} [Field F] [NumberField F]

section Expansion

variable {ι : Type} [Fintype ι] {χ χ' : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)}
  {α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)}
  {f : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ} {σ' : ℝ} {Φ : AdelicGL2 (𝓞 F) F → ℂ} {κ : ℂ}

private theorem apply_diagOne_mul_eq_sum (hαn : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (hind : ∀ (e : ι) (τ : ℝ), IsInducedSection (𝓞 F) F (etaFst (χ e) α hα ((σ' : ℂ) + (τ : ℂ) * Complex.I))
      (etaSnd (χ' e) α hα ((σ' : ℂ) + (τ : ℂ) * Complex.I)) (f e ((σ' : ℂ) + (τ : ℂ) * Complex.I)))
    (hrep : ∀ g, Φ g = ∑ e, κ * ∫ τ : ℝ, f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g)
    (t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Φ (diagOne t * g) = ∑ e, ((χ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      MellinParseval.lineProfile σ' (fun τ : ℝ => κ * f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g) (ideleNorm F t) := by
  rw [hrep]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← integral_const_mul]
  refine MellinParseval.integral_mul_cpow_add_half_mul' σ' _ _ _ (ideleNorm_pos (F := F) t) (fun τ => ?_)
  show κ * f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) (diagOne t * g) =
    ((χ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ ((σ' : ℂ) + (τ : ℂ) * Complex.I + 1 / 2) *
      (κ * f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g)
  rw [IwasawaSectionValues.eta_apply_diagOne_mul (hind e τ) t g, hαn t]
  ring

private theorem apply_mul_eq_of_sum {H : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hrep : ∀ g, Φ g = ∑ e, κ * ∫ τ : ℝ, f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g)
    (hinv : ∀ (e : ι) (τ : ℝ), ∀ x ∈ H, ∀ g : AdelicGL2 (𝓞 F) F,
      f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) (x * g) = f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g) :
    ∀ x ∈ H, ∀ g : AdelicGL2 (𝓞 F) F, Φ (x * g) = Φ g := by
  intro x hx g
  rw [hrep, hrep]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ => hinv e τ x hx g)

private theorem apply_centralScalar_mul_eq_of_sum {ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ}
    (hrep : ∀ g, Φ g = ∑ e, κ * ∫ τ : ℝ, f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g)
    (hcen : ∀ (e : ι) (τ : ℝ) (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) (centralScalar (𝓞 F) F z * g) =
        ((ξ z : ℂˣ) : ℂ) * f e ((σ' : ℂ) + (τ : ℂ) * Complex.I) g)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Φ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * Φ g := by
  rw [hrep, hrep, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [integral_congr_ae (Filter.Eventually.of_forall fun τ => hcen e τ z g), integral_const_mul]
  ring

private theorem apply_centralScalar_mul_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ} (hprod : ∀ z, χ₁ z * χ₂ z = ξ z)
    {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : IsInducedSection (𝓞 F) F χ₁ χ₂ h)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    h (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * h g := by
  rw [isInducedSection_centralScalar_mul hh z g, ← Units.val_mul, hprod z]

private theorem etaFst_apply_mul_etaSnd_apply (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (z : (AdeleRing (𝓞 F) F)ˣ) :
    etaFst μ α hα s z * etaSnd ν α hα s z = μ z * ν z := by
  exact etaFst_mul_etaSnd μ ν α hα s z

end Expansion
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section Domination

variable {ι : Type} [Fintype ι] {K : Type*} [MeasurableSpace K]

private theorem norm_sum_mul_mul_le {χ : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)} (hχu : ∀ e, IsUnitaryChar (𝓞 F) F (χ e))
    (t : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ) (L : ι → ℂ) :
    ‖∑ e, ((χ e t : ℂˣ) : ℂ) * w * L e‖ ≤ ‖w‖ * ∑ e, ‖L e‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun e _ => ?_))
  rw [norm_mul, norm_mul, hχu e t, one_mul]

private theorem norm_cpow_half_mul_self {y : ℝ} (hy : 0 < y) :
    ‖((y : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ * ‖((y : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ = y := by
  rw [← norm_mul, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hy.ne'), add_halves, Complex.cpow_one,
    Complex.norm_of_nonneg hy.le]

private theorem norm_mul_conj_le {χ₁ χ₂ : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)}
    (hχ₁ : ∀ e, IsUnitaryChar (𝓞 F) F (χ₁ e)) (hχ₂ : ∀ e, IsUnitaryChar (𝓞 F) F (χ₂ e))
    (t : (AdeleRing (𝓞 F) F)ˣ) {X Y : ℂ} {L₁ L₂ : ι → ℂ}
    (hX : X = ∑ e, ((χ₁ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) * L₁ e)
    (hY : Y = ∑ e, ((χ₂ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) * L₂ e) :
    ‖X * starRingEnd ℂ Y‖ ≤ ideleNorm F t * ∑ e, ∑ e', ‖L₁ e‖ * ‖L₂ e'‖ := by
  have h1 := norm_sum_mul_mul_le hχ₁ t (((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ)) L₁
  have h2 := norm_sum_mul_mul_le hχ₂ t (((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ)) L₂
  rw [norm_mul, Complex.norm_conj, hX, hY]
  refine (mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun e _ => norm_nonneg _))).trans (le_of_eq ?_)
  rw [mul_mul_mul_comm, norm_cpow_half_mul_self (ideleNorm_pos (F := F) t), Finset.sum_mul_sum]

private def dominant (L₁ L₂ : ι → K → ℝ → ℂ) (p : ℝ × K) : ℝ :=
  p.1 * ∑ e, ∑ e', ‖L₁ e p.2 p.1‖ * ‖L₂ e' p.2 p.1‖

private theorem measurable_dominant {L₁ L₂ : ι → K → ℝ → ℂ}
    (hL₁m : ∀ e, StronglyMeasurable fun p : ℝ × K => L₁ e p.2 p.1)
    (hL₂m : ∀ e, StronglyMeasurable fun p : ℝ × K => L₂ e p.2 p.1) : Measurable (dominant L₁ L₂) := by
  refine measurable_fst.mul (Finset.measurable_sum _ fun e _ => Finset.measurable_sum _ fun e' _ => ?_)
  exact (hL₁m e).norm.measurable.mul (hL₂m e').norm.measurable

private theorem integrable_inv_mul_inv_mul_dominant {m : Measure K} {L₁ L₂ : ι → K → ℝ → ℂ}
    (hL₁m : ∀ e, StronglyMeasurable fun p : ℝ × K => L₁ e p.2 p.1)
    (hL₂m : ∀ e, StronglyMeasurable fun p : ℝ × K => L₂ e p.2 p.1)
    (hL : ∀ e e', Integrable (fun p : ℝ × K => ((p.1⁻¹ : ℝ) : ℂ) * (L₁ e p.2 p.1 * starRingEnd ℂ (L₂ e' p.2 p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    Integrable (fun p : ℝ × K => p.1⁻¹ * (p.1⁻¹ * dominant L₁ L₂ p)) ((volume.restrict (Set.Ioi (0 : ℝ))).prod m) := by
  have hsum : Integrable (fun p : ℝ × K => ∑ e, ∑ e',
      ‖((p.1⁻¹ : ℝ) : ℂ) * (L₁ e p.2 p.1 * starRingEnd ℂ (L₂ e' p.2 p.1))‖)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m) :=
    integrable_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ => (hL e e').norm
  refine hsum.mono'
    (measurable_fst.inv.mul (measurable_fst.inv.mul (measurable_dominant hL₁m hL₂m))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have hS0 : 0 ≤ ∑ e, ∑ e', ‖L₁ e p.2 p.1‖ * ‖L₂ e' p.2 p.1‖ :=
    Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun e' _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hterm : ∀ e e', ‖((p.1⁻¹ : ℝ) : ℂ) * (L₁ e p.2 p.1 * starRingEnd ℂ (L₂ e' p.2 p.1))‖ =
      |p.1⁻¹| * (‖L₁ e p.2 p.1‖ * ‖L₂ e' p.2 p.1‖) := fun e e' => by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [dominant]
  rcases eq_or_ne p.1 0 with h0 | h0
  · simp [h0]
  · rw [inv_mul_cancel_left₀ h0, Real.norm_eq_abs, abs_mul, abs_of_nonneg hS0]
    simp_rw [Finset.mul_sum]
    exact le_rfl

private theorem integrable_mul_conj_withDensity_prod [SFinite (NumberField.Idele.idelicHaar F)]
    (hnorm : Measurable (ideleNorm F)) {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (m : Measure K) [SFinite m]
    {χ₁ χ₂ : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)}
    (hχ₁ : ∀ e, IsUnitaryChar (𝓞 F) F (χ₁ e)) (hχ₂ : ∀ e, IsUnitaryChar (𝓞 F) F (χ₂ e))
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {gk : K → AdelicGL2 (𝓞 F) F}
    (hHm : AEStronglyMeasurable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × K => Φ₁ (diagOne p.1 * gk p.2) * starRingEnd ℂ (Φ₂ (diagOne p.1 * gk p.2)))
      (((NumberField.Idele.idelicHaar F).restrict D).prod m))
    {L₁ L₂ : ι → K → ℝ → ℂ}
    (hP : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : K), Φ₁ (diagOne t * gk k) =
      ∑ e, ((χ₁ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) * L₁ e k (ideleNorm F t))
    (hQ : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : K), Φ₂ (diagOne t * gk k) =
      ∑ e, ((χ₂ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) * L₂ e k (ideleNorm F t))
    (hL₁m : ∀ e, StronglyMeasurable fun p : ℝ × K => L₁ e p.2 p.1)
    (hL₂m : ∀ e, StronglyMeasurable fun p : ℝ × K => L₂ e p.2 p.1)
    (hL : ∀ e e', Integrable (fun p : ℝ × K => ((p.1⁻¹ : ℝ) : ℂ) * (L₁ e p.2 p.1 * starRingEnd ℂ (L₂ e' p.2 p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod m)) :
    Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × K => Φ₁ (diagOne p.1 * gk p.2) * starRingEnd ℂ (Φ₂ (diagOne p.1 * gk p.2)))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
        fun t => ENNReal.ofReal (ideleNorm F t)⁻¹).prod m) :=
  NormDisintegration.integrable_withDensity_prod_of_norm_le hnorm hV hVT m hHm (G₀ := dominant L₁ L₂)
    (measurable_dominant hL₁m hL₂m)
    (fun t k => show _ ≤ ideleNorm F t * ∑ e, ∑ e', ‖L₁ e k (ideleNorm F t)‖ * ‖L₂ e' k (ideleNorm F t)‖ from
      norm_mul_conj_le hχ₁ hχ₂ t (hP t k) (hQ t k))
    (integrable_inv_mul_inv_mul_dominant hL₁m hL₂m hL)

end Domination
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end TorusExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

open AutomorphicForm
open scoped ENNReal

namespace CuspidalOrthogonality

section OrbitSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

private theorem setIntegral_out_mul_conj_out_eq_zero (μ : Measure G) (H : Subgroup G) (μH : Measure H)
    (S : Set (MulAction.orbitRel.Quotient H G)) (φ c : G → ℂ)
    (hinv : ∀ h ∈ H, ∀ g : G, c (h * g) = c g) (hc : ∀ᵐ g ∂μ, c g = 0) :
    ∫ q in S, φ q.out * starRingEnd ℂ (c q.out) ∂(HaarQuotient.measure μ H μH) = 0 := by
  have hout : ∀ g : G, c (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = c g := by
    intro g
    have hmem : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g :=
      MulAction.orbitRel_apply.mp (Quotient.mk_out' (s₁ := MulAction.orbitRel H G) g)
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp hmem
    have hx' : (x : G) * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := hx
    rw [← hx']
    exact hinv x x.2 g
  have hlin : ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ ∂((HaarQuotient.measure μ H μH).restrict S)
      = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ ∂((HaarQuotient.measure μ H μH).restrict S)
        ≤ ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ ∂(HaarQuotient.measure μ H μH) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ
            ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
              (μ.withDensity (HaarQuotient.density H μH))) := rfl
      _ ≤ ∫⁻ g, ‖φ (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out
            * starRingEnd ℂ (c (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out)‖ₑ
            ∂(μ.withDensity (HaarQuotient.density H μH)) :=
          lintegral_map_le _ _
      _ = ∫⁻ _g, (0 : ℝ≥0∞) ∂(μ.withDensity (HaarQuotient.density H μH)) := by
          refine lintegral_congr_ae ?_
          have hc' : ∀ᵐ g ∂(μ.withDensity (HaarQuotient.density H μH)), c g = 0 :=
            (withDensity_absolutelyContinuous μ (HaarQuotient.density H μH)).ae_le hc
          filter_upwards [hc'] with g hg
          rw [hout g, hg, map_zero, mul_zero, enorm_zero]
      _ = 0 := lintegral_zero
  have hle := enorm_integral_le_lintegral_enorm (μ := (HaarQuotient.measure μ H μH).restrict S)
    (fun q : MulAction.orbitRel.Quotient H G => φ q.out * starRingEnd ℂ (c q.out))
  rw [hlin, nonpos_iff_eq_zero, enorm_eq_zero] at hle
  exact hle

end OrbitSpace
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section Invariance

variable (F : Type) [Field F] [NumberField F]

private def leftInvariantSubgroup (c : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {h | ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g}
  one_mem' := by
    intro g
    rw [one_mul]
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    have hb' : ∀ g : AdelicGL2 (𝓞 F) F, c (b * g) = c g := hb
    intro g
    rw [mul_assoc, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    intro g
    have h := ha' (a⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    exact h.symm

private theorem mem_leftInvariantSubgroup {c : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} :
    h ∈ leftInvariantSubgroup F c ↔ ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g :=
  Iff.rfl

omit [NumberField F] in

private theorem scalar_mem_borelSubgroup (a : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a ∈ borelSubgroup F := by
  show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  have hval : ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (a : F) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

omit [NumberField F] in

private theorem diagOne_mem_borelSubgroup (a : Fˣ) : diagOne a ∈ borelSubgroup F := by
  show ((diagOne a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem forall_mem_rationalTorusUnipotent_mul_eq (c : AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), c (unipotentGL2 x * g) = c g)
    (hB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, c (globalPoints (𝓞 F) F γ * g) = c g) :
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g := by
  have hle : rationalTorusUnipotent F ≤ leftInvariantSubgroup F c := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (scalar_mem_borelSubgroup F a) g
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (diagOne_mem_borelSubgroup F a) g
    · rintro _ ⟨x, rfl⟩ g
      exact hN x.toAdd g
  intro h hh g
  have hmem : h ∈ leftInvariantSubgroup F c := hle hh
  exact (mem_leftInvariantSubgroup F).mp hmem g

private abbrev pinsAt (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private theorem constantTerm_rationalTorusUnipotent_mul (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (pinsAt F Φ).Z →* ℂˣ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsAutomorphicFnAt F (pinsAt F Φ) ξ f) :
    letI := (pinsAt F Φ).nS
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      constantTerm (pinsAt F Φ).ν unipotentGL2 f (h * g) = constantTerm (pinsAt F Φ).ν unipotentGL2 f g := by
  have hls : IsLsXiFunction (𝓞 F) F (pinsAt F Φ).Z ξ f := by
    letI := (pinsAt F Φ).mS
    exact ((lsXiMemberAt_iff (𝓞 F) F (pinsAt F Φ).μ (pinsAt F Φ).Z ξ (pinsAt F Φ).D f).mp hf).1
  have hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      f (globalPoints (𝓞 F) F γ * g) = f g := hls.left_invariant
  letI := (pinsAt F Φ).nS
  refine forall_mem_rationalTorusUnipotent_mul_eq F (constantTerm (pinsAt F Φ).ν unipotentGL2 f) ?_ ?_
  · intro x g
    exact constantTerm_adelicBox_unipotentGL2_mul F (fun k h => hleft (unipotentGL2 k) h) x g
  · intro γ hγ g
    exact constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F (fun γ' _ h => hleft γ' h) hγ g

private theorem setIntegral_slabQuotient_eq_zero_of_ae_constantTerm_eq_zero (d₁ d₂ : ℝ)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pinsAt F Φ).Z →* ℂˣ) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsAutomorphicFnAt F (pinsAt F Φ) ξ f)
    (hcusp : letI := (pinsAt F Φ).mS
      letI := (pinsAt F Φ).nS
      ∀ᵐ g ∂(pinsAt F Φ).μ, constantTerm (pinsAt F Φ).ν unipotentGL2 f g = 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    letI := (pinsAt F Φ).mS
    letI := (pinsAt F Φ).nS
    ∫ q in {q : RationalTorusUnipotentQuotient F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂},
        φ q.out * starRingEnd ℂ (constantTerm (pinsAt F Φ).ν unipotentGL2 f q.out)
      ∂(rationalTorusUnipotentQuotientMeasure F) = 0 :=
  setIntegral_out_mul_conj_out_eq_zero (pinsAt F Φ).μ (rationalTorusUnipotent F)
    (rationalTorusUnipotentHaar F) _ φ _ (constantTerm_rationalTorusUnipotent_mul F Φ ξ f hf) hcusp

end Invariance
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end CuspidalOrthogonality
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace EisensteinTorusFacts

section Determinant

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem coe_diagOne (t : (AdeleRing R K)ˣ) :
    ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.diagonal ![(t : AdeleRing R K), 1] := rfl

private theorem
det_diagOne (t : (AdeleRing R K)ˣ) : Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 R K) = t := by
  apply Units.ext
  show Matrix.det ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = (t : AdeleRing R K)
  rw [coe_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_centralScalar (z : (AdeleRing R K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar R K z) = z ^ 2 := by
  rw [show centralScalar R K = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

end Determinant
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

variable {F : Type} [Field F] [NumberField F]

private theorem ideleNorm_det_iwasawa (z t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * k)) =
      NumberField.TateGlobal.ideleNorm F z ^ 2 *
        (NumberField.TateGlobal.ideleNorm F t *
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k)) := by
  rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    det_centralScalar, det_diagOne, pow_two, NumberField.TateGlobal.ideleNorm_mul]
  ring

private theorem iwasawa_mem_slab_iff (d₁ d₂ : ℝ) (z t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * diagOne t * k ∈
        {g : AdelicGL2 (𝓞 F) F |
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ↔
      NumberField.TateGlobal.ideleNorm F z ^ 2 *
          (NumberField.TateGlobal.ideleNorm F t *
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k)) ∈ Set.Icc d₁ d₂ := by
  rw [Set.mem_setOf_eq, ideleNorm_det_iwasawa]

private theorem ideleNorm_mul_ideleNorm_det_pos (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    0 < NumberField.TateGlobal.ideleNorm F t *
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k) :=
  mul_pos (NumberField.TateGlobal.ideleNorm_pos (F := F) t) (NumberField.TateGlobal.ideleNorm_pos (F := F) _)

private theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [one_mul] at h
  have h' : NumberField.TateGlobal.ideleNorm F 1 * 1 =
      NumberField.TateGlobal.ideleNorm F 1 * NumberField.TateGlobal.ideleNorm F 1 := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := F) 1).ne' h').symm

private theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
  ext
  simp [unipotentGL2, Matrix.det_fin_two_of]

private theorem ideleNorm_det_mul_eq_of_mem :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (x * g)) =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  have h := CuspidalOrthogonality.forall_mem_rationalTorusUnipotent_mul_eq F
    (fun g : AdelicGL2 (𝓞 F) F =>
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ))
    (fun x g => by
      simp only [map_mul, det_unipotentGL2, one_mul])
    (fun γ _ g => by
      simp only [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints, one_mul])
  intro x hx g
  have h' := h x hx g
  beta_reduce at h'
  exact_mod_cast h'

private theorem measurableSet_setOf_ideleNorm_det_out_mem_Icc (d₁ d₂ : ℝ)
    (hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hdesc : ∀ (P : AdelicGL2 (𝓞 F) F → Prop), Measurable P →
      (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, P (x * g) = P g) →
        Measurable fun q : RationalTorusUnipotentQuotient F => P q.out) :
    MeasurableSet {q : RationalTorusUnipotentQuotient F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂} :=
  measurableSet_setOf.2 (hdesc _ (measurableSet_setOf.1 hS)
    (fun x hx g => by rw [ideleNorm_det_mul_eq_of_mem x hx g]))

private theorem apply_mul_of_mem_of_isSlabProfile {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : AutomorphicForm.IsSlabProfile F Z ξ φ) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, φ (x * g) = φ g :=
  CuspidalOrthogonality.forall_mem_rationalTorusUnipotent_mul_eq F φ hφ.unipotent_mul hφ.borel_mul

private theorem apply_globalPoints_mul_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (h₁ : IsIdeleClassChar (𝓞 F) F χ₁) (h₂ : IsIdeleClassChar (𝓞 F) F χ₂) :
    ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, f (globalPoints (𝓞 F) F γ * g) = f g := by
  intro γ hγ g
  have hmem : globalPoints (𝓞 F) F γ ∈ adelicBorel (𝓞 F) F := globalPoints_mem_adelicBorel (R := 𝓞 F) (K := F) hγ
  rw [hf _ hmem g, borelDiagFst_globalPoints (R := 𝓞 F) (K := F) hγ hmem,
    borelDiagSnd_globalPoints (R := 𝓞 F) (K := F) hγ hmem, h₁, h₂]
  simp

private theorem apply_mul_of_mem_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (h₁ : IsIdeleClassChar (𝓞 F) F χ₁) (h₂ : IsIdeleClassChar (𝓞 F) F χ₂) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g :=
  CuspidalOrthogonality.forall_mem_rationalTorusUnipotent_mul_eq F f
    (fun x g => isInducedSection_unipotent_mul hf x g) (apply_globalPoints_mul_of_isInducedSection hf h₁ h₂)

section Characters

variable {ι G M : Type*}

private theorem exists_apply_ne_of_mul_eq [Group M] {μ ν : ι → G → M} {ξ : G → M} {P : G → Prop}
    (hμν : ∀ e x, μ e x * ν e x = ξ x)
    (hdist : ∀ e e' : ι, e ≠ e' → ∃ x, P x ∧ (μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)) :
    ∀ e e' : ι, e ≠ e' → ∃ x, P x ∧ μ e x ≠ μ e' x := by
  intro e e' hne
  obtain ⟨x, hx, h⟩ := hdist e e' hne
  rcases h with h | h
  · exact ⟨x, hx, h⟩
  · refine ⟨x, hx, fun hμ => h ?_⟩
    rw [eq_inv_mul_of_mul_eq (hμν e x), eq_inv_mul_of_mul_eq (hμν e' x), hμ]

private theorem involutive_of_swap {μ ν : ι → G → M} {r : ι → ι} (hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
    (hsep : ∀ e e' : ι, e ≠ e' → μ e ≠ μ e' ∨ ν e ≠ ν e') : Function.Involutive r := by
  intro e
  by_contra h
  rcases hsep _ _ h with h' | h'
  · exact h' (by rw [(hr (r e)).1, (hr e).2])
  · exact h' (by rw [(hr (r e)).2, (hr e).1])

private theorem ne_or_ne_of_exists {μ ν : ι → G → M} {P : G → Prop}
    (hdist : ∀ e e' : ι, e ≠ e' → ∃ x, P x ∧ (μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)) :
    ∀ e e' : ι, e ≠ e' → μ e ≠ μ e' ∨ ν e ≠ ν e' := by
  intro e e' hne
  obtain ⟨x, -, h⟩ := hdist e e' hne
  rcases h with h | h
  · exact Or.inl fun heq => h (by rw [heq])
  · exact Or.inr fun heq => h (by rw [heq])

end Characters
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

private theorem norm_xi_eq_one {ι : Type*} {μ ν : ι → (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ} (hμν : ∀ e x, μ e x * ν e x = ξ x)
    (hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e)) (e : ι)
    (x : (AdeleRing (𝓞 F) F)ˣ) : ‖((ξ x : ℂˣ) : ℂ)‖ = 1 := by
  rw [← hμν e x, Units.val_mul, norm_mul, hμ e x, hν e x, one_mul]

private theorem mul_conj_apply_centralScalar_mul {ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ} (hξ : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      Φ₁ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * Φ₁ g)
    (h₂ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      Φ₂ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * Φ₂ g)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Φ₁ (centralScalar (𝓞 F) F z * g) * starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * g)) =
      Φ₁ g * starRingEnd ℂ (Φ₂ g) := by
  have hu : ((ξ z : ℂˣ) : ℂ) * starRingEnd ℂ ((ξ z : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ z]
    simp
  rw [h₁, h₂, map_mul]
  linear_combination (Φ₁ g * starRingEnd ℂ (Φ₂ g)) * hu

private theorem mul_conj_apply_iwasawa {ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ} (hξ : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      Φ₁ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * Φ₁ g)
    (h₂ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      Φ₂ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * Φ₂ g)
    (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
        starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
      Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))) := by
  rw [mul_assoc]
  exact mul_conj_apply_centralScalar_mul hξ h₁ h₂ z _

private theorem eq_zero_of_sum_empty {ι : Type*} [Fintype ι] [IsEmpty ι] {X : Type*} {φ : X → ℂ} {c : ι → X → ℂ}
    (hrep : ∀ g, φ g = ∑ e, c e g) (g : X) : φ g = 0 := by
  rw [hrep g]
  exact Finset.sum_of_isEmpty _

end EisensteinTorusFacts
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace SectionLineFamily

private theorem measurable_ofReal_cpow {α : Type*} [MeasurableSpace α] {g : α → ℝ} {h : α → ℂ} (hg : Measurable g)
    (hh : Measurable h) : Measurable fun x => ((g x : ℝ) : ℂ) ^ h x := by
  simp only [Complex.cpow_def]
  refine Measurable.ite ((Complex.measurable_ofReal.comp hg) (measurableSet_singleton (0 : ℂ))) ?_ ?_
  · exact Measurable.ite (hh (measurableSet_singleton (0 : ℂ))) measurable_const measurable_const
  · exact Complex.measurable_exp.comp ((Complex.measurable_log.comp (Complex.measurable_ofReal.comp hg)).mul hh)

private theorem lineProfile_eq_rpow_mul (a : ℝ → ℂ) (σ₁ σ' : ℝ) {y : ℝ} (hy : 0 < y) :
    MellinParseval.lineProfile σ' a y = ((y ^ (σ' - σ₁) : ℝ) : ℂ) * MellinParseval.lineProfile σ₁ a y := by
  unfold MellinParseval.lineProfile
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [Complex.ofReal_cpow hy.le, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  congr 2
  push_cast
  ring

private theorem norm_lineProfile_eq_rpow_mul (a : ℝ → ℂ) (σ₁ σ' : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖MellinParseval.lineProfile σ' a y‖ = y ^ (σ' - σ₁) * ‖MellinParseval.lineProfile σ₁ a y‖ := by
  rw [lineProfile_eq_rpow_mul a σ₁ σ' hy, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _)]

private theorem hasIntegrableProfile_of_abscissa {a : ℝ → ℂ} {σ₁ : ℝ} (h : MellinParseval.HasIntegrableProfile σ₁ a)
    (σ' : ℝ) : MellinParseval.HasIntegrableProfile σ' a := by
  unfold MellinParseval.HasIntegrableProfile at h ⊢
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy : (0 : ℝ) < y := hy
  simp only [smul_eq_mul]
  rw [lineProfile_eq_rpow_mul a σ₁ σ' hy, ← mul_assoc, ← Complex.ofReal_mul, StripContour.rpow_neg_div_mul_rpow hy,
    show y ^ (-σ₁) / y = y ^ (σ' - σ₁ - σ' - 1) by
      rw [show σ' - σ₁ - σ' - 1 = -σ₁ + (-1 : ℝ) by ring, Real.rpow_add hy, Real.rpow_neg_one, div_eq_mul_inv]]

private theorem norm_lineProfile_le_rpow_mul_integral {a : ℝ → ℂ} {ma : ℝ → ℝ} (hma : Integrable ma)
    (ha : ∀ u, ‖a u‖ ≤ ma u) (σ' : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖MellinParseval.lineProfile σ' a y‖ ≤ y ^ σ' * ∫ u, ma u := by
  unfold MellinParseval.lineProfile
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hma.const_mul _) (Filter.Eventually.of_forall fun u => ?_)
  rw [StripContour.norm_cpow_smul hy]
  exact mul_le_mul_of_nonneg_left (ha u) (Real.rpow_nonneg hy.le _)

variable {X : Type*} {K : Type*}

private def lineFamily (f : ℂ → X → ℂ) (ι : K → X) (κ : ℂ) (σ : ℝ) (c : K) (τ : ℝ) : ℂ :=
  κ * f ((σ : ℂ) + (τ : ℂ) * Complex.I) (ι c)

private theorem lineFamily_apply (f : ℂ → X → ℂ) (ι : K → X) (κ : ℂ) (σ : ℝ) (c : K) (τ : ℝ) :
    lineFamily f ι κ σ c τ = κ * f ((σ : ℂ) + (τ : ℂ) * Complex.I) (ι c) :=
  rfl

variable [TopologicalSpace X]

private theorem continuous_lineFamily {f : ℂ → X → ℂ} (hjc : Continuous fun p : ℂ × X => f p.1 p.2) {ι : K → X}
    (κ : ℂ) (σ : ℝ) (c : K) : Continuous (lineFamily f ι κ σ c) := by
  show Continuous fun τ : ℝ => κ * f ((σ : ℂ) + (τ : ℂ) * Complex.I) (ι c)
  exact continuous_const.mul (hjc.comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).prodMk continuous_const))

private theorem continuous_lineFamily_uncurry [TopologicalSpace K] {f : ℂ → X → ℂ}
    (hjc : Continuous fun p : ℂ × X => f p.1 p.2) {ι : K → X}
    (hι : Continuous ι) (κ : ℂ) (σ : ℝ) : Continuous fun p : ℝ × K => lineFamily f ι κ σ p.2 p.1 := by
  show Continuous fun p : ℝ × K => κ * f ((σ : ℂ) + (p.1 : ℂ) * Complex.I) (ι p.2)
  exact continuous_const.mul (hjc.comp
    ((continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).prodMk
      (hι.comp continuous_snd)))

private theorem
measurable_lineFamily_prod [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K] {f : ℂ → X → ℂ}
    (hjc : Continuous fun p : ℂ × X => f p.1 p.2) {ι : K → X} (hι : Continuous ι) (κ : ℂ) (σ : ℝ) :
    Measurable fun q : (ℝ × K) × ℝ => lineFamily f ι κ σ q.1.2 q.2 := by
  have h : Continuous fun q : (ℝ × K) × ℝ => lineFamily f ι κ σ q.1.2 q.2 :=
    (continuous_lineFamily_uncurry hjc hι κ σ).comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact h.measurable

private theorem exists_majorant {f : ℂ → X → ℂ}
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ R : ℝ) :
    ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ' - σ| < R → ∀ (c : K) (τ : ℝ), ‖κ * f ((σ' : ℂ) + (τ : ℂ) * Complex.I) (ι c)‖ ≤ ‖κ‖ * m τ := by
  obtain ⟨m, hm, hB, hb⟩ := hdec (|σ| + R) C hC
  refine ⟨m, hm, hB, fun σ' hσ' c τ => ?_⟩
  have h1 := abs_lt.1 hσ'
  have h2 := le_abs_self σ
  have h3 := neg_abs_le σ
  have hσ'' : |σ'| ≤ |σ| + R := abs_le.2 ⟨by linarith, by linarith⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb σ' hσ'' τ (ι c) (hιC c)) (norm_nonneg κ)

private theorem integrable_lineFamily {f : ℂ → X → ℂ} (hjc : Continuous fun p : ℂ × X => f p.1 p.2)
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ : ℝ) (c : K) :
    Integrable (lineFamily f ι κ σ c) := by
  obtain ⟨m, hm, -, hb⟩ := exists_majorant hdec hC hιC κ σ 1
  refine (hm.const_mul ‖κ‖).mono' (continuous_lineFamily hjc κ σ c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  exact hb σ (by simp) c τ

private theorem hasIntegrableProfile_lineFamily {f : ℂ → X → ℂ} (hhol : ∀ g, Differentiable ℂ fun s => f s g)
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ : ℝ) (c : K) :
    MellinParseval.HasIntegrableProfile σ (lineFamily f ι κ σ c) := by
  obtain ⟨m, hm, -, hb⟩ := exists_majorant hdec hC hιC κ σ 1
  have hf : DifferentiableOn ℂ (fun s : ℂ => κ * f s (ι c)) {s : ℂ | |s.re - σ| < 1} :=
    ((hhol (ι c)).const_mul κ).differentiableOn
  have h := StripContour.hasIntegrableProfile_of_differentiableOn one_pos hf (hm.const_mul ‖κ‖)
    (fun σ' hσ' τ => hb σ' hσ' c τ)
  exact h

private theorem hasIntegrableProfile_lineFamily' {f : ℂ → X → ℂ} (hhol : ∀ g, Differentiable ℂ fun s => f s g)
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ : ℝ) (c : K) (σ' : ℝ) :
    MellinParseval.HasIntegrableProfile σ' (lineFamily f ι κ σ c) :=
  hasIntegrableProfile_of_abscissa (hasIntegrableProfile_lineFamily hhol hdec hC hιC κ σ c) σ'

private theorem exists_norm_lineProfile_lineFamily_le {f : ℂ → X → ℂ} (hhol : ∀ g, Differentiable ℂ fun s => f s g)
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ σ' : ℝ) :
    ∃ M : ℝ, ∀ (c : K) {y : ℝ}, 0 < y →
      ‖MellinParseval.lineProfile σ' (lineFamily f ι κ σ c) y‖ ≤ M * y ^ (σ' - 1) ∧
      ‖MellinParseval.lineProfile σ' (lineFamily f ι κ σ c) y‖ ≤ M * y ^ (σ' + 1) := by
  obtain ⟨m, hm, -, hb⟩ := exists_majorant hdec hC hιC κ σ 2
  refine ⟨∫ t, ‖κ‖ * m t, fun c y hy => ?_⟩
  have hf : DifferentiableOn ℂ (fun s : ℂ => κ * f s (ι c)) {s : ℂ | |s.re - σ| < 2} :=
    ((hhol (ι c)).const_mul κ).differentiableOn
  have hbound : ∀ σ'' : ℝ, |σ'' - σ| < 2 → ∀ t : ℝ,
      ‖(fun s : ℂ => κ * f s (ι c)) ((σ'' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ‖κ‖ * m t :=
    fun σ'' hσ'' t => hb σ'' hσ'' c t
  have hσσ : |σ - σ| < (2 : ℝ) := by simp
  have hlo : |σ - 1 - σ| < (2 : ℝ) := by rw [show σ - 1 - σ = (-1 : ℝ) by ring]; norm_num
  have hhi : |σ + 1 - σ| < (2 : ℝ) := by rw [show σ + 1 - σ = (1 : ℝ) by ring]; norm_num
  have h₁ := StripContour.norm_lineProfile_le hf (hm.const_mul ‖κ‖) hbound hσσ hlo hy
  have h₂ := StripContour.norm_lineProfile_le hf (hm.const_mul ‖κ‖) hbound hσσ hhi hy
  have hM : (0 : ℝ) ≤ ∫ t, ‖κ‖ * m t :=
    integral_nonneg fun t => le_trans (norm_nonneg _) (hb σ (by simp) c t)
  have hpow : (0 : ℝ) ≤ y ^ (σ' - σ) := Real.rpow_nonneg hy.le _
  rw [norm_lineProfile_eq_rpow_mul _ σ σ' hy]
  constructor
  · calc y ^ (σ' - σ) * ‖MellinParseval.lineProfile σ (lineFamily f ι κ σ c) y‖
        ≤ y ^ (σ' - σ) * (y ^ (σ - 1) * ∫ t, ‖κ‖ * m t) := mul_le_mul_of_nonneg_left h₁ hpow
      _ = (∫ t, ‖κ‖ * m t) * y ^ (σ' - 1) := by
          rw [← mul_assoc, ← Real.rpow_add hy, show σ' - σ + (σ - 1) = σ' - 1 by ring, mul_comm]
  · calc y ^ (σ' - σ) * ‖MellinParseval.lineProfile σ (lineFamily f ι κ σ c) y‖
        ≤ y ^ (σ' - σ) * (y ^ (σ + 1) * ∫ t, ‖κ‖ * m t) := mul_le_mul_of_nonneg_left h₂ hpow
      _ = (∫ t, ‖κ‖ * m t) * y ^ (σ' + 1) := by
          rw [← mul_assoc, ← Real.rpow_add hy, show σ' - σ + (σ + 1) = σ' + 1 by ring, mul_comm]

private def tailMajorant (A : ℝ) (y : ℝ) : ℝ :=
  A * (if y ≤ 1 then (1 : ℝ) else y ^ (-2 : ℝ))

private theorem integrableOn_tailMajorant (A : ℝ) : IntegrableOn (tailMajorant A) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_const (C := A) measure_Ioc_lt_top.ne).congr_fun (fun y hy => ?_) measurableSet_Ioc
    simp [tailMajorant, hy.2]
  · refine IntegrableOn.congr_fun
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul A)
      (fun y hy => ?_) measurableSet_Ioi
    have hy' : ¬ y ≤ 1 := not_le.mpr hy
    simp [tailMajorant, hy']

private theorem le_tailMajorant {σ₁' σ₂' : ℝ} (hσ : σ₁' + σ₂' = 0) {M I : ℝ} (hM : 0 ≤ M) {y : ℝ} (hy : 0 < y)
    {a b : ℝ} (hb : 0 ≤ b) (ha₁ : a ≤ M * y ^ (σ₁' - 1)) (ha₂ : a ≤ M * y ^ (σ₁' + 1))
    (hb' : b ≤ y ^ σ₂' * I) : y⁻¹ * (a * b) ≤ tailMajorant (M * I) y := by
  have hyinv : (0 : ℝ) ≤ y⁻¹ := inv_nonneg.mpr hy.le
  unfold tailMajorant
  split_ifs with h1
  · calc y⁻¹ * (a * b) ≤ y⁻¹ * ((M * y ^ (σ₁' + 1)) * (y ^ σ₂' * I)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul ha₂ hb' hb (by positivity)) hyinv
      _ = M * I * (y⁻¹ * y ^ (σ₁' + 1 + σ₂')) := by rw [Real.rpow_add hy (σ₁' + 1) σ₂']; ring
      _ = M * I * 1 := by
          rw [show σ₁' + 1 + σ₂' = (1 : ℝ) by linarith, Real.rpow_one, inv_mul_cancel₀ hy.ne']
  · calc y⁻¹ * (a * b) ≤ y⁻¹ * ((M * y ^ (σ₁' - 1)) * (y ^ σ₂' * I)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul ha₁ hb' hb (by positivity)) hyinv
      _ = M * I * (y⁻¹ * y ^ (σ₁' - 1 + σ₂')) := by rw [Real.rpow_add hy (σ₁' - 1) σ₂']; ring
      _ = M * I * y ^ (-2 : ℝ) := by
          rw [show σ₁' - 1 + σ₂' = (-1 : ℝ) by linarith, Real.rpow_neg_one,
            show (-2 : ℝ) = (-1) + (-1) by norm_num, Real.rpow_add hy, Real.rpow_neg_one]

private theorem stronglyMeasurable_lineProfile_lineFamily
    [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K] {f : ℂ → X → ℂ}
    (hjc : Continuous fun p : ℂ × X => f p.1 p.2) {ι : K → X} (hι : Continuous ι) (κ : ℂ) (σ σ' : ℝ) :
    StronglyMeasurable fun p : ℝ × K => MellinParseval.lineProfile σ' (lineFamily f ι κ σ p.2) p.1 := by
  have hker : Measurable fun q : (ℝ × K) × ℝ => ((q.1.1 : ℝ) : ℂ) ^ ((σ' : ℂ) + (q.2 : ℂ) * Complex.I) :=
    measurable_ofReal_cpow (measurable_fst.comp measurable_fst)
      (measurable_const.add ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const))
  have hG : Measurable fun q : (ℝ × K) × ℝ =>
      (((q.1.1 : ℝ) : ℂ) ^ ((σ' : ℂ) + (q.2 : ℂ) * Complex.I)) • lineFamily f ι κ σ q.1.2 q.2 :=
    hker.smul (measurable_lineFamily_prod hjc hι κ σ)
  unfold MellinParseval.lineProfile
  exact StronglyMeasurable.integral_prod_right'
    (f := fun q : (ℝ × K) × ℝ =>
      (((q.1.1 : ℝ) : ℂ) ^ ((σ' : ℂ) + (q.2 : ℂ) * Complex.I)) • lineFamily f ι κ σ q.1.2 q.2)
    hG.stronglyMeasurable

private theorem stronglyMeasurable_lineProfile_of_measurable [MeasurableSpace K] {b : K → ℝ → ℂ}
    (hbm : Measurable fun p : ℝ × K => b p.2 p.1) (σ' : ℝ) :
    StronglyMeasurable fun p : ℝ × K => MellinParseval.lineProfile σ' (b p.2) p.1 := by
  have hker : Measurable fun q : (ℝ × K) × ℝ => ((q.1.1 : ℝ) : ℂ) ^ ((σ' : ℂ) + (q.2 : ℂ) * Complex.I) :=
    measurable_ofReal_cpow (measurable_fst.comp measurable_fst)
      (measurable_const.add ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const))
  have hb' : Measurable fun q : (ℝ × K) × ℝ => b q.1.2 q.2 :=
    hbm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hG : Measurable fun q : (ℝ × K) × ℝ =>
      (((q.1.1 : ℝ) : ℂ) ^ ((σ' : ℂ) + (q.2 : ℂ) * Complex.I)) • b q.1.2 q.2 :=
    hker.smul hb'
  unfold MellinParseval.lineProfile
  exact StronglyMeasurable.integral_prod_right'
    (f := fun q : (ℝ × K) × ℝ => (((q.1.1 : ℝ) : ℂ) ^ ((σ' : ℂ) + (q.2 : ℂ) * Complex.I)) • b q.1.2 q.2)
    hG.stronglyMeasurable

private theorem integrable_inv_mul_lineProfile_mul_conj_lineProfile
    [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    {f : ℂ → X → ℂ} (hjc : Continuous fun p : ℂ × X => f p.1 p.2) (hhol : ∀ g, Differentiable ℂ fun s => f s g)
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hι : Continuous ι) (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ : ℝ)
    {σ₁' σ₂' : ℝ} (hσ : σ₁' + σ₂' = 0) {b : K → ℝ → ℂ} (hbm : Measurable fun p : ℝ × K => b p.2 p.1)
    (hbd : ∃ mb : ℝ → ℝ, Integrable mb ∧ (∃ B : ℝ, ∀ u, mb u ≤ B) ∧ ∀ (u : ℝ) (c : K), ‖b c u‖ ≤ mb u)
    (m : Measure K) [IsFiniteMeasure m] :
    Integrable (fun p : ℝ × K => ((p.1⁻¹ : ℝ) : ℂ) *
        (MellinParseval.lineProfile σ₁' (lineFamily f ι κ σ p.2) p.1 *
          conj (MellinParseval.lineProfile σ₂' (b p.2) p.1)))
      ((volume.restrict (Ioi (0 : ℝ))).prod m) := by
  obtain ⟨mb, hmb, -, hb⟩ := hbd
  obtain ⟨M₀, hM₀⟩ := exists_norm_lineProfile_lineFamily_le hhol hdec hC hιC κ σ σ₁'
  have hM : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hM' : ∀ (c : K) {y : ℝ}, 0 < y →
      ‖MellinParseval.lineProfile σ₁' (lineFamily f ι κ σ c) y‖ ≤ max M₀ 0 * y ^ (σ₁' - 1) ∧
      ‖MellinParseval.lineProfile σ₁' (lineFamily f ι κ σ c) y‖ ≤ max M₀ 0 * y ^ (σ₁' + 1) := by
    intro c y hy
    obtain ⟨h₁, h₂⟩ := hM₀ c hy
    exact ⟨h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)),
      h₂.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _))⟩

  have hBb : ∀ (c : K) {y : ℝ}, 0 < y →
      ‖MellinParseval.lineProfile σ₂' (b c) y‖ ≤ y ^ σ₂' * ∫ u, mb u :=
    fun c y hy => norm_lineProfile_le_rpow_mul_integral hmb (fun u => hb u c) σ₂' hy

  have hμ : (volume.restrict (Ioi (0 : ℝ))).prod m = (volume.prod m).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]

  have hmeas : AEStronglyMeasurable (fun p : ℝ × K => ((p.1⁻¹ : ℝ) : ℂ) *
      (MellinParseval.lineProfile σ₁' (lineFamily f ι κ σ p.2) p.1 *
        conj (MellinParseval.lineProfile σ₂' (b p.2) p.1))) ((volume.restrict (Ioi (0 : ℝ))).prod m) := by
    have h1 : Measurable fun p : ℝ × K => ((p.1⁻¹ : ℝ) : ℂ) := Complex.measurable_ofReal.comp measurable_fst.inv
    exact h1.aestronglyMeasurable.mul
      ((stronglyMeasurable_lineProfile_lineFamily hjc hι κ σ σ₁').aestronglyMeasurable.mul
        (Complex.continuous_conj.comp_aestronglyMeasurable
          (stronglyMeasurable_lineProfile_of_measurable hbm σ₂').aestronglyMeasurable))

  have hmaj : Integrable (fun p : ℝ × K => tailMajorant (max M₀ 0 * ∫ u, mb u) p.1 * (1 : ℝ))
      ((volume.restrict (Ioi (0 : ℝ))).prod m) :=
    Integrable.mul_prod (integrableOn_tailMajorant (max M₀ 0 * ∫ u, mb u)) (integrable_const (1 : ℝ))
  refine hmaj.mono' hmeas ?_
  rw [hμ]
  refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
  have hy : (0 : ℝ) < p.1 := hp.1
  obtain ⟨ha₁, ha₂⟩ := hM' p.2 hy
  have hkey := le_tailMajorant hσ hM hy (norm_nonneg (MellinParseval.lineProfile σ₂' (b p.2) p.1)) ha₁ ha₂
    (hBb p.2 hy)
  calc ‖((p.1⁻¹ : ℝ) : ℂ) * (MellinParseval.lineProfile σ₁' (lineFamily f ι κ σ p.2) p.1 *
          conj (MellinParseval.lineProfile σ₂' (b p.2) p.1))‖
      = p.1⁻¹ * (‖MellinParseval.lineProfile σ₁' (lineFamily f ι κ σ p.2) p.1‖ *
          ‖MellinParseval.lineProfile σ₂' (b p.2) p.1‖) := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hy.le)]
    _ ≤ tailMajorant (max M₀ 0 * ∫ u, mb u) p.1 := hkey
    _ = tailMajorant (max M₀ 0 * ∫ u, mb u) p.1 * (1 : ℝ) := (mul_one _).symm

private theorem integrable_lineFamily_mul_conj
    [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K] {f : ℂ → X → ℂ}
    (hjc : Continuous fun p : ℂ × X => f p.1 p.2)
    (hdec : ∀ (σ₀ : ℝ) (C : Set X), IsCompact C → ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
      ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    {C : Set X} (hC : IsCompact C) {ι : K → X} (hι : Continuous ι) (hιC : ∀ c, ι c ∈ C) (κ : ℂ) (σ : ℝ)
    {b : K → ℝ → ℂ} (hbm : Measurable fun p : ℝ × K => b p.2 p.1)
    (hbd : ∃ mb : ℝ → ℝ, Integrable mb ∧ (∃ B : ℝ, ∀ u, mb u ≤ B) ∧ ∀ (u : ℝ) (c : K), ‖b c u‖ ≤ mb u)
    (m : Measure K) [IsFiniteMeasure m] :
    Integrable (fun p : ℝ × K => lineFamily f ι κ σ p.2 p.1 * conj (b p.2 p.1)) (volume.prod m) := by
  obtain ⟨mb, -, ⟨Bb, hBb⟩, hb⟩ := hbd
  obtain ⟨ma, hma, -, ha⟩ := exists_majorant hdec hC hιC κ σ 1
  have hmeas : AEStronglyMeasurable (fun p : ℝ × K => lineFamily f ι κ σ p.2 p.1 * conj (b p.2 p.1))
      (volume.prod m) :=
    (continuous_lineFamily_uncurry hjc hι κ σ).aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hbm.aestronglyMeasurable)
  have hmaj : Integrable (fun p : ℝ × K => ‖κ‖ * ma p.1 * Bb) (volume.prod m) := by
    have h := Integrable.mul_prod (hma.const_mul ‖κ‖) (integrable_const (μ := m) Bb)
    exact h
  refine hmaj.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_mul, Complex.norm_conj]
  have h₁ : ‖lineFamily f ι κ σ p.2 p.1‖ ≤ ‖κ‖ * ma p.1 := ha σ (by simp) p.2 p.1
  have h₂ : ‖b p.2 p.1‖ ≤ Bb := (hb p.1 p.2).trans (hBb p.1)
  exact mul_le_mul h₁ h₂ (norm_nonneg _) (le_trans (norm_nonneg _) h₁)

end SectionLineFamily
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing"

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open scoped Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

noncomputable section

namespace IwasawaQuotientDisintegration

variable (F : Type) [Field F] [NumberField F]

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

private theorem adelicWeyl_mem_range : adelicWeyl (𝓞 F) F ∈ (globalPoints (𝓞 F) F).range :=
  ⟨gl2Weyl, rfl⟩

private theorem adelicWeyl_mul_unipotentGL2_mem_range (β : F) :
    adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) ∈ (globalPoints (𝓞 F) F).range :=
  ⟨gl2Weyl * unipotentGL2 β, by rw [map_mul, globalPoints_unipotentGL2]; rfl⟩

private def bruhatSummand : Option F → (globalPoints (𝓞 F) F).range
  | none => 1
  | some β => ⟨_, adelicWeyl_mul_unipotentGL2_mem_range F β⟩

private def bruhatRep (i : Option F) : (globalPoints (𝓞 F) F).range :=
  (bruhatSummand F i)⁻¹

@[scoped simp]
private theorem bruhatRep_inv (i : Option F) : (bruhatRep F i)⁻¹ = bruhatSummand F i :=
  inv_inv _

private theorem bruhatRep_none_inv_smul (g : AdelicGL2 (𝓞 F) F) :
    ((bruhatRep F none : AdelicGL2 (𝓞 F) F)⁻¹) • g = g := by
  simp [bruhatRep, bruhatSummand]

private theorem bruhatRep_some_inv_smul (β : F) (g : AdelicGL2 (𝓞 F) F) :
    ((bruhatRep F (some β) : AdelicGL2 (𝓞 F) F)⁻¹) • g
      = adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g := by
  simp [bruhatRep, bruhatSummand, smul_eq_mul]

private theorem borel_map_le_range : (borelSubgroup F).map (globalPoints (𝓞 F) F) ≤ (globalPoints (𝓞 F) F).range :=
  Subgroup.map_le_range _ _

omit [NumberField F] in

private theorem summand_mul_entry (γ₀ : GL (Fin 2) F) :
    (((1 : GL (Fin 2) F) * γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
    ∀ β : F, ((gl2Weyl * unipotentGL2 β * γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0
      = (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 + β * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  refine ⟨by simp, fun β => ?_⟩
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem bruhatSummand_eq_globalPoints :
    ((bruhatSummand F none : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F 1) ∧
    ∀ β : F, (bruhatSummand F (some β) : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 β) := by
  refine ⟨by simp [bruhatSummand], fun β => ?_⟩
  simp only [bruhatSummand, map_mul, globalPoints_unipotentGL2]
  rfl

private theorem globalPoints_mem_borel_map_iff (x₀ : GL (Fin 2) F) :
    globalPoints (𝓞 F) F x₀ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)
      ↔ (x₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
    have hentry := congrArg (fun y : AdelicGL2 (𝓞 F) F => (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) hbx
    simp only [globalPoints_apply, hb', map_zero] at hentry
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (by simpa using hentry.symm)
  · intro h
    exact ⟨x₀, h, rfl⟩

private theorem bruhatRep_spec (γ : (globalPoints (𝓞 F) F).range) :
    ∃! i : Option F, ((bruhatRep F i)⁻¹ * γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  obtain ⟨h1, hw⟩ := summand_mul_entry F γ₀
  obtain ⟨s1, sw⟩ := bruhatSummand_eq_globalPoints F

  have key : ∀ i : Option F,
      (((bruhatRep F i)⁻¹ * γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)) ↔
      (match i with
        | none => (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        | some β => (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 + β * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) := by
    intro i

    rw [bruhatRep_inv, ← hγ₀]
    cases i with
    | none => rw [s1, ← map_mul, globalPoints_mem_borel_map_iff, h1]
    | some β => rw [sw β, ← map_mul, globalPoints_mem_borel_map_iff, hw β]
  have hdet : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1
      - (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have := (Matrix.isUnits_det_units γ₀).ne_zero
    rwa [Matrix.det_fin_two] at this
  by_cases hc : (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  ·
    have ha : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro ha; apply hdet; rw [ha, hc]; ring
    refine ⟨none, (key none).2 hc, fun i hi => ?_⟩
    cases i with
    | none => rfl
    | some β =>
      exfalso
      have := (key (some β)).1 hi
      simp only [hc, mul_zero, add_zero] at this
      exact ha this
  ·
    refine ⟨some (-(γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0), ?_, fun i hi => ?_⟩
    · refine (key _).2 ?_
      simp only [div_mul_cancel₀ _ hc, add_neg_cancel]
    · cases i with
      | none => exact absurd ((key none).1 hi) hc
      | some β =>
        have hβ := (key (some β)).1 hi
        congr 1
        field_simp
        linear_combination hβ

private theorem isFundamentalDomain_iUnion_bruhatRep (μ : Measure (AdelicGL2 (𝓞 F) F))
    [SMulInvariantMeasure (AdelicGL2 (𝓞 F) F) (AdelicGL2 (𝓞 F) F) μ]
    [Countable F] [Countable (globalPoints (𝓞 F) F).range] (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ μ) :
    IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F))
      (⋃ i : Option F, ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹) • Φ) μ :=
  hΦ.iUnion_inv_smul_of_leftCosetRepresentatives μ _ _ (borel_map_le_range F) Φ (bruhatRep F) (bruhatRep_spec F)

private theorem countable_numberField : Countable F :=
  Countable.of_equiv (Fin (Module.finrank ℚ F) → ℚ) (Module.finBasis ℚ F).equivFun.symm.toEquiv

private theorem countable_globalPoints_range : Countable (globalPoints (𝓞 F) F).range := by
  haveI := countable_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective _).countable

private theorem exists_isFundamentalDomain_borelImage :
    ∃ S : Set (AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := countable_numberField F
  haveI := countable_globalPoints_range F
  obtain ⟨D, hD⟩ := exists_isFundamentalDomain_globalPoints_range F
  exact ⟨_, isFundamentalDomain_iUnion_bruhatRep F (adelicGLHaar (Fin 2) (𝓞 F) F) D hD⟩

private theorem countable_principalIdeles : Countable (M4aHerbrand.principalIdeles (𝓞 F) F) := by
  haveI := countable_numberField F
  haveI : Countable Fˣ := Units.val_injective.countable
  unfold M4aHerbrand.principalIdeles
  exact (MonoidHom.rangeRestrict_surjective _).countable

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI := countable_numberField F
  have hsurj : Function.Surjective
      (fun a : F => (⟨algebraMap F (AdeleRing (𝓞 F) F) a, a, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨x, a, rfl⟩
    exact ⟨a, rfl⟩
  exact hsurj.countable

private theorem secondCountableTopology_units_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_units_adeleRing F
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  infer_instance

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  infer_instance

private abbrev iwPt (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    AdelicGL2 (𝓞 F) F :=
  unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)

private abbrev wt (t : (AdeleRing (𝓞 F) F)ˣ) : ℝ≥0∞ := ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)

private theorem wt_ne_zero (t : (AdeleRing (𝓞 F) F)ˣ) : wt F t ≠ 0 :=
  (ENNReal.ofReal_pos.2 (inv_pos.2 (NumberField.TateGlobal.ideleNorm_pos t))).ne'

private theorem distribHaarChar_eq_one_of_mem_principalIdeles {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) : distribHaarChar (AdeleRing (𝓞 F) F) γ = 1 := by
  obtain ⟨η, rfl⟩ := MonoidHom.mem_range.mp hγ
  exact NumberField.AdeleRing.distribHaarChar_algebraMap F η

private theorem _root_.IwasawaQuotientDisintegration.ideleNorm_eq_one_of_mem_principalIdeles {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) : NumberField.TateGlobal.ideleNorm F γ = 1 := by
  simp [NumberField.TateGlobal.ideleNorm, distribHaarChar_eq_one_of_mem_principalIdeles F hγ]

p2m_export "IwasawaQuotientDisintegration" "ideleNorm_eq_one_of_mem_principalIdeles"

private theorem wt_mul_of_mem_principalIdeles {γ : (AdeleRing (𝓞 F) F)ˣ} (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F)
    (t : (AdeleRing (𝓞 F) F)ˣ) : wt F (γ * t) = wt F t := by
  simp only [wt, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_eq_one_of_mem_principalIdeles F hγ, one_mul]

private theorem lintegral_smul_adelicAddHaar_of_distribHaarChar_eq_one {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : distribHaarChar (AdeleRing (𝓞 F) F) γ = 1) (Ξ : AdeleRing (𝓞 F) F → ℝ≥0∞) :
    ∫⁻ y, Ξ (γ • y) ∂(adelicAddHaar (𝓞 F) F) = ∫⁻ y, Ξ y ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  let e : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F := (Homeomorph.smul γ).toMeasurableEquiv
  have hmap : Measure.map e (adelicAddHaar (𝓞 F) F) = adelicAddHaar (𝓞 F) F := by
    ext A hA
    rw [Measure.map_apply e.measurable hA]
    have hpre : e ⁻¹' A = γ⁻¹ • A := Set.preimage_smul γ A
    have hinv : distribHaarChar (AdeleRing (𝓞 F) F) γ⁻¹ = 1 := by rw [map_inv, hγ, inv_one]
    rw [hpre, ← distribHaarChar_mul (adelicAddHaar (𝓞 F) F) γ⁻¹ A, hinv, ENNReal.coe_one, one_mul]
  calc ∫⁻ y, Ξ (γ • y) ∂(adelicAddHaar (𝓞 F) F)
      = ∫⁻ y, Ξ y ∂(Measure.map e (adelicAddHaar (𝓞 F) F)) := (lintegral_map_equiv Ξ e).symm
    _ = ∫⁻ y, Ξ y ∂(adelicAddHaar (𝓞 F) F) := by rw [hmap]

private theorem continuous_diagOne : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (diagOne t : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F) := by
  have hdiag : ∀ x : AdeleRing (𝓞 F) F, Matrix.scalar (Fin 2) x = Matrix.diagonal fun _ => x := fun x =>
    Matrix.scalar_apply x
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
    simp only [hdiag]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp only [hdiag]
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

private theorem measurable_centralScalar_mul_diagOne_mul :
    Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      centralScalar (𝓞 F) F p.1 * diagOne p.2.1 * (p.2.2 : AdelicGL2 (𝓞 F) F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have h1 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      centralScalar (𝓞 F) F p.1 := (continuous_centralScalar F).measurable.comp measurable_fst
  have h2 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      (diagOne p.2.1 : AdelicGL2 (𝓞 F) F) :=
    (continuous_diagOne F).measurable.comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      (p.2.2 : AdelicGL2 (𝓞 F) F) :=
    (measurable_subtype_val_adelicMaximalCompact F).comp (measurable_snd.comp measurable_snd)
  exact (h1.mul h2).mul h3

private theorem measurable_iwPt_comp {α : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F} (hα : Measurable α)
    {αu αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαu : Measurable αu) (hαt : Measurable αt) :
    Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      iwPt F (α q.1.1.1) (αu q.1.1.2) (αt q.1.2) q.2 := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hn : Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) ×
      adelicMaximalCompact F => (unipotentGL2 (α q.1.1.1) : AdelicGL2 (𝓞 F) F) :=
    (continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).measurable.comp
      (hα.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  have hz : Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) ×
      adelicMaximalCompact F => centralScalar (𝓞 F) F (αu q.1.1.2) :=
    (continuous_centralScalar F).measurable.comp (hαu.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  have hd : Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) ×
      adelicMaximalCompact F => (diagOne (αt q.1.2) : AdelicGL2 (𝓞 F) F) :=
    (continuous_diagOne F).measurable.comp (hαt.comp (measurable_snd.comp measurable_fst))
  have hk : Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) ×
      adelicMaximalCompact F => (q.2 : AdelicGL2 (𝓞 F) F) :=
    (measurable_subtype_val_adelicMaximalCompact F).comp measurable_snd
  exact ((hn.mul hz).mul hd).mul hk

private theorem measurable_wt_comp {αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαt : Measurable αt) :
    Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      wt F (αt q.1.2) :=
  ENNReal.measurable_ofReal.comp
    (((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp
      (hαt.comp (measurable_snd.comp measurable_fst))).inv)

private theorem measurable_integrand {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ)
    {α : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F} (hα : Measurable α)
    {αu αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαu : Measurable αu) (hαt : Measurable αt) :
    Measurable fun q : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      φ (iwPt F (α q.1.1.1) (αu q.1.1.2) (αt q.1.2) q.2) * wt F (αt q.1.2) :=
  (hφ.comp (measurable_iwPt_comp F hα hαu hαt)).mul (measurable_wt_comp F hαt)

private theorem measurable_lintegral_k {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ)
    {α : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F} (hα : Measurable α)
    {αu αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαu : Measurable αu) (hαt : Measurable αt) :
    Measurable fun p : (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k, φ (iwPt F (α p.1.1) (αu p.1.2) (αt p.2) k) * wt F (αt p.2) ∂(maximalCompactHaar F) :=
  (measurable_integrand F hφ hα hαu hαt).lintegral_prod_right'

private theorem measurable_lintegral_t {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ)
    {α : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F} (hα : Measurable α)
    {αu αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαu : Measurable αu) (hαt : Measurable αt)
    (νt : Measure (AdeleRing (𝓞 F) F)ˣ) [SFinite νt] :
    Measurable fun p : AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t, ∫⁻ k, φ (iwPt F (α p.1) (αu p.2) (αt t) k) * wt F (αt t) ∂(maximalCompactHaar F) ∂νt :=
  (measurable_lintegral_k F hφ hα hαu hαt).lintegral_prod_right'

private theorem measurable_lintegral_u {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ)
    {α : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F} (hα : Measurable α)
    {αu αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαu : Measurable αu) (hαt : Measurable αt)
    (νu νt : Measure (AdeleRing (𝓞 F) F)ˣ) [SFinite νu] [SFinite νt] :
    Measurable fun x : AdeleRing (𝓞 F) F =>
      ∫⁻ u, ∫⁻ t, ∫⁻ k, φ (iwPt F (α x) (αu u) (αt t) k) * wt F (αt t) ∂(maximalCompactHaar F) ∂νt ∂νu :=
  (measurable_lintegral_t F hφ hα hαu hαt νt).lintegral_prod_right'

private theorem measurable_lintegral_t_fixed {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ)
    {αu αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαu : Measurable αu) (hαt : Measurable αt)
    (νt : Measure (AdeleRing (𝓞 F) F)ˣ) [SFinite νt] (x : AdeleRing (𝓞 F) F) :
    Measurable fun u : (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t, ∫⁻ k, φ (iwPt F x (αu u) (αt t) k) * wt F (αt t) ∂(maximalCompactHaar F) ∂νt := by
  have hx : Measurable fun u : (AdeleRing (𝓞 F) F)ˣ => ((x, u) : AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_lintegral_t F hφ measurable_id' hαu hαt νt).fun_comp hx
  exact h

private theorem measurable_lintegral_k_fixed {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ)
    {αt : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ} (hαt : Measurable αt)
    (x : AdeleRing (𝓞 F) F) (u : (AdeleRing (𝓞 F) F)ˣ) :
    Measurable fun t : (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k, φ (iwPt F x u (αt t) k) * wt F (αt t) ∂(maximalCompactHaar F) := by
  have hx : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ =>
      (((x, u), t) : (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_lintegral_k F hφ measurable_id' measurable_id' hαt).fun_comp hx
  exact h

private theorem measurable_integrand_fixed {φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hφ : Measurable φ) (x : AdeleRing (𝓞 F) F)
    (u t : (AdeleRing (𝓞 F) F)ˣ) : Measurable fun k : adelicMaximalCompact F => φ (iwPt F x u t k) * wt F t := by
  have hq : Measurable fun k : adelicMaximalCompact F =>
      ((((x, u), t), k) :
        ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F) :=
    measurable_const.prodMk measurable_id
  have hk := (measurable_iwPt_comp F measurable_id' measurable_id' measurable_id').fun_comp hq
  have h := (hφ.fun_comp hk).mul (measurable_const (a := wt F t))
  exact h

private theorem measurable_dilate_translate (γ : (AdeleRing (𝓞 F) F)ˣ) (β : AdeleRing.principalSubgroup (𝓞 F) F) :
    Measurable fun x : AdeleRing (𝓞 F) F => γ • ((-β) +ᵥ x) := by
  have h : Continuous fun x : AdeleRing (𝓞 F) F =>
      (γ : AdeleRing (𝓞 F) F) * (((-β : AdeleRing.principalSubgroup (𝓞 F) F) : AdeleRing (𝓞 F) F) + x) :=
    continuous_const.mul (continuous_const.add continuous_id)
  exact h.measurable

private theorem measurable_units_mul_left (γ : (AdeleRing (𝓞 F) F)ˣ) :
    Measurable fun u : (AdeleRing (𝓞 F) F)ˣ => γ * u :=
  (continuous_const.mul continuous_id).measurable

private theorem measurable_subgroup_smul (Γ : Subgroup (AdeleRing (𝓞 F) F)ˣ) (γ : Γ) :
    Measurable fun u : (AdeleRing (𝓞 F) F)ˣ => γ • u :=
  measurable_units_mul_left F (γ : (AdeleRing (𝓞 F) F)ˣ)

private abbrev Idx : Type :=
  M4aHerbrand.principalIdeles (𝓞 F) F × M4aHerbrand.principalIdeles (𝓞 F) F × AdeleRing.principalSubgroup (𝓞 F) F

private abbrev coordElt (i : Idx F) : AdelicGL2 (𝓞 F) F :=
  unipotentGL2 ((i.2.2 : AdeleRing.principalSubgroup (𝓞 F) F) : AdeleRing (𝓞 F) F) *
    centralScalar (𝓞 F) F (i.1 : (AdeleRing (𝓞 F) F)ˣ) * diagOne (i.2.1 : (AdeleRing (𝓞 F) F)ˣ)

private theorem globalPoints_scalar (a : Fˣ) :
    globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPoints, centralScalar, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]

private theorem globalPoints_diagOne (b : Fˣ) :
    globalPoints (𝓞 F) F (diagOne b) =
      diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, diagOne_coe_apply]

private theorem coordElt_coe (i : Idx F) :
    ((coordElt F i : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      !![((i.1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * ((i.2.1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F),
          ((i.2.2 : AdeleRing.principalSubgroup (𝓞 F) F) : AdeleRing (𝓞 F) F) *
            ((i.1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F);
        0, ((i.1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [centralScalar, Matrix.GeneralLinearGroup.scalar, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two,
        diagOne_coe_apply, Matrix.scalar_apply]

private theorem coordElt_mem (i : Idx F) : coordElt F i ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  obtain ⟨⟨d, a, ha⟩, ⟨s, b, hb⟩, ⟨β, r, hr⟩⟩ := i
  refine ⟨unipotentGL2 r * Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagOne b, ?_, ?_⟩
  · show ((unipotentGL2 r * Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagOne b : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Matrix.GeneralLinearGroup.scalar, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply,
      Matrix.scalar_apply]
  · simp only [coordElt, map_mul, globalPoints_unipotentGL2, globalPoints_scalar, globalPoints_diagOne, ha, hb, hr]

private theorem coordElt_injective : Function.Injective (coordElt F) := by
  rintro ⟨d, s, β⟩ ⟨d', s', β'⟩ h
  have hM := congrArg (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) h
  simp only [coordElt_coe] at hM
  have h11 := congrFun (congrFun hM 1) 1
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at h11 h00 h01
  have hd : d = d' := Subtype.ext (Units.ext h11)
  subst hd
  have hs : s = s' := Subtype.ext (Units.ext ((Units.mul_right_inj (d : (AdeleRing (𝓞 F) F)ˣ)).1 h00))
  have hβ : β = β' := Subtype.ext ((Units.mul_left_inj (d : (AdeleRing (𝓞 F) F)ˣ)).1 h01)
  rw [hs, hβ]

private theorem exists_coordElt_eq {γ : AdelicGL2 (𝓞 F) F} (hγ : γ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)) :
    ∃ i : Idx F, coordElt F i = γ := by
  obtain ⟨m, hm, rfl⟩ := hγ
  have hm' : (m : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hm
  have hdet : (m : Matrix (Fin 2) (Fin 2) F) 0 0 * (m : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have := (Matrix.isUnits_det_units m).ne_zero
    rwa [Matrix.det_fin_two, hm', mul_zero, sub_zero] at this
  have ha₀ : (m : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd₀ : (m : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨⟨⟨_, Units.mk0 _ hd₀, rfl⟩,
    ⟨_, Units.mk0 ((m : Matrix (Fin 2) (Fin 2) F) 0 0 / (m : Matrix (Fin 2) (Fin 2) F) 1 1) (div_ne_zero ha₀ hd₀),
      rfl⟩,
    ⟨_, (m : Matrix (Fin 2) (Fin 2) F) 0 1 / (m : Matrix (Fin 2) (Fin 2) F) 1 1, rfl⟩⟩, ?_⟩
  simp only [coordElt]
  rw [← globalPoints_unipotentGL2, ← globalPoints_scalar, ← globalPoints_diagOne, ← map_mul, ← map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.scalar, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply,
      Matrix.scalar_apply, hm'] <;> field_simp

private noncomputable def coordEquiv : Idx F ≃ (borelSubgroup F).map (globalPoints (𝓞 F) F) :=
  Equiv.ofBijective (fun i => ⟨coordElt F i, coordElt_mem F i⟩)
    ⟨fun i j h => coordElt_injective F (congrArg Subtype.val h),
      fun γ => by obtain ⟨i, hi⟩ := exists_coordElt_eq F γ.2; exact ⟨i, Subtype.ext hi⟩⟩

private theorem coordEquiv_apply_coe (i : Idx F) : ((coordEquiv F i : (borelSubgroup F).map (globalPoints (𝓞 F) F)) :
    AdelicGL2 (𝓞 F) F) = coordElt F i := rfl

private theorem countable_idx : Countable (Idx F) := by
  haveI := countable_principalIdeles F
  haveI := countable_principalSubgroup F
  infer_instance

private theorem coordElt_mul_iwPt (i : Idx F) (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ)
    (k : adelicMaximalCompact F) :
    coordElt F i * iwPt F x u t k =
      iwPt F (((i.2.2 : AdeleRing.principalSubgroup (𝓞 F) F) : AdeleRing (𝓞 F) F) +
          ((i.2.1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x)
        ((i.1 : (AdeleRing (𝓞 F) F)ˣ) * u) ((i.2.1 : (AdeleRing (𝓞 F) F)ˣ) * t) k := by
  have key : coordElt F i * (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t) =
      unipotentGL2 (((i.2.2 : AdeleRing.principalSubgroup (𝓞 F) F) : AdeleRing (𝓞 F) F) +
          ((i.2.1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) *
        centralScalar (𝓞 F) F ((i.1 : (AdeleRing (𝓞 F) F)ˣ) * u) * diagOne ((i.2.1 : (AdeleRing (𝓞 F) F)ˣ) * t) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
        simp [centralScalar, Matrix.GeneralLinearGroup.scalar, unipotentGL2, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_two, diagOne_coe_apply, Matrix.scalar_apply] <;> ring
  calc coordElt F i * iwPt F x u t k
      = coordElt F i * (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t) * (k : AdelicGL2 (𝓞 F) F) := by
        simp only [iwPt, mul_assoc]
    _ = _ := by rw [key]

private theorem coordElt_inv_mul_iwPt (i : Idx F) (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ)
    (k : adelicMaximalCompact F) :
    (coordElt F i)⁻¹ * iwPt F x u t k =
      iwPt F (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x)) (i.1⁻¹ • u)
        (i.2.1⁻¹ • t) k := by
  rw [inv_mul_eq_iff_eq_mul, coordElt_mul_iwPt]
  simp [Units.smul_def, Subgroup.smul_def, AddSubgroup.vadd_def, mul_add]

private theorem coordElt_mem_rationalTorusUnipotent (i : Idx F) : coordElt F i ∈ rationalTorusUnipotent F :=
  (isFundamentalDomain_boxSheet_rationalTorusUnipotent F).1 (coordElt_mem F i)

private theorem unipotentGL2_mem_rationalTorusUnipotent (x : AdeleRing (𝓞 F) F) :
    (unipotentGL2 x : AdelicGL2 (𝓞 F) F) ∈ rationalTorusUnipotent F :=
  Subgroup.mem_sup_right ⟨Multiplicative.ofAdd x, rfl⟩

private theorem apply_iwPt_of_invariant {f : AdelicGL2 (𝓞 F) F → ℝ≥0∞}
    (hfH : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g)
    (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    f (iwPt F x u t k) = f (centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) := by
  have h := hfH _ (unipotentGL2_mem_rationalTorusUnipotent F x)
    (centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F))
  simpa only [iwPt, mul_assoc] using h

private theorem ae_tsum_indicator_inv_mul_eq_one {S S' : Set (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS' : S' =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] S) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      ∑' γ : (borelSubgroup F).map (globalPoints (𝓞 F) F),
        S'.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : AdelicGL2 (𝓞 F) F)⁻¹ * g) = 1 := by
  classical
  haveI : Countable ((borelSubgroup F).map (globalPoints (𝓞 F) F)) :=
    (isFundamentalDomain_boxSheet_rationalTorusUnipotent F).2.1

  have hdiff : ∀ γ : (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      ((γ : AdelicGL2 (𝓞 F) F)⁻¹ * g ∈ S' ↔ (γ : AdelicGL2 (𝓞 F) F)⁻¹ * g ∈ S) := by
    intro γ
    have h1 : adelicGLHaar (Fin 2) (𝓞 F) F
        ((fun g => (γ : AdelicGL2 (𝓞 F) F)⁻¹ * g) ⁻¹' {g | ¬ (g ∈ S' ↔ g ∈ S)}) = 0 := by
      rw [measure_preimage_mul]
      have : {g | ¬ (g ∈ S' ↔ g ∈ S)} = {g | g ∈ S' ∧ g ∉ S} ∪ {g | g ∈ S ∧ g ∉ S'} := by
        ext g; by_cases h' : g ∈ S' <;> by_cases h : g ∈ S <;> simp [h', h]
      rw [this]
      refine measure_union_null ?_ ?_
      · exact (ae_eq_set.1 hS').1
      · exact (ae_eq_set.1 hS').2
    have h2 := (measure_eq_zero_iff_ae_notMem.1 h1)
    filter_upwards [h2] with g hg
    simpa using hg

  have hcov : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ γ : (borelSubgroup F).map (globalPoints (𝓞 F) F),
      (γ : AdelicGL2 (𝓞 F) F)⁻¹ * g ∈ S := by
    filter_upwards [hS.ae_covers] with g hg
    obtain ⟨γ, hγ⟩ := hg
    exact ⟨γ⁻¹, by simpa [Subgroup.smul_def] using hγ⟩
  have huniq : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∀ γ₁ γ₂ : (borelSubgroup F).map (globalPoints (𝓞 F) F),
      (γ₁ : AdelicGL2 (𝓞 F) F)⁻¹ * g ∈ S → (γ₂ : AdelicGL2 (𝓞 F) F)⁻¹ * g ∈ S → γ₁ = γ₂ := by
    rw [ae_all_iff]; intro γ₁
    rw [ae_all_iff]; intro γ₂
    by_cases h12 : γ₁ = γ₂
    · exact Filter.Eventually.of_forall fun _ _ _ => h12
    · have hnull : adelicGLHaar (Fin 2) (𝓞 F) F (γ₁ • S ∩ γ₂ • S) = 0 := hS.aedisjoint h12
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with g hg h1 h2
      exact absurd ⟨Set.mem_smul_set_iff_inv_smul_mem.2 h1, Set.mem_smul_set_iff_inv_smul_mem.2 h2⟩ hg
  filter_upwards [ae_all_iff.2 hdiff, hcov, huniq] with g hdiffg hcovg huniqg
  obtain ⟨γ₀, hγ₀⟩ := hcovg
  rw [tsum_eq_single γ₀]
  · simp [(hdiffg γ₀).2 hγ₀]
  · intro γ hγ
    have : (γ : AdelicGL2 (𝓞 F) F)⁻¹ * g ∉ S' := fun hmem => hγ (huniqg γ γ₀ ((hdiffg γ).1 hmem) hγ₀)
    simp [this]

private theorem ae_iwPt_notMem_of_measure_eq_zero {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F))
    {N : Set (AdelicGL2 (𝓞 F) F)} (hN : adelicGLHaar (Fin 2) (𝓞 F) F N = 0) :
    ∀ᵐ x ∂(adelicAddHaar (𝓞 F) F), ∀ᵐ u ∂(NumberField.Idele.idelicHaar F), ∀ᵐ t ∂(NumberField.Idele.idelicHaar F),
      ∀ᵐ k ∂(maximalCompactHaar F), iwPt F x u t k ∉ N := by
  haveI := sigmaFinite_idelicHaar F
  set N' : Set (AdelicGL2 (𝓞 F) F) := toMeasurable (adelicGLHaar (Fin 2) (𝓞 F) F) N with hN'def
  clear_value N'
  have hN'm : MeasurableSet N' := by rw [hN'def]; exact measurableSet_toMeasurable _ _
  have hN'0 : adelicGLHaar (Fin 2) (𝓞 F) F N' = 0 := by rw [hN'def, measure_toMeasurable]; exact hN
  have hNN' : N ⊆ N' := by rw [hN'def]; exact subset_toMeasurable _ _
  have hφ : Measurable (N'.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞)) := measurable_one.indicator hN'm
  have hformula := hc _ hφ
  rw [lintegral_indicator_one hN'm, hN'0] at hformula
  have hzero : ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
      N'.indicator 1 (iwPt F x u t k) * wt F t
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ∂(adelicAddHaar (𝓞 F) F) = 0 := by
    rcases mul_eq_zero.1 hformula.symm with h | h
    · exact absurd h hc0
    · exact h
  have hmx : Measurable fun x : AdeleRing (𝓞 F) F => ∫⁻ u, ∫⁻ t, ∫⁻ k, N'.indicator 1 (iwPt F x u t k) * wt F t
      ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    measurable_lintegral_u F hφ measurable_id' measurable_id' measurable_id' (NumberField.Idele.idelicHaar F)
      (NumberField.Idele.idelicHaar F)
  have hx := (lintegral_eq_zero_iff' hmx.aemeasurable).1 hzero
  filter_upwards [hx] with x hx0
  have hmu : Measurable fun u : (AdeleRing (𝓞 F) F)ˣ => ∫⁻ t, ∫⁻ k, N'.indicator 1 (iwPt F x u t k) * wt F t
      ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    measurable_lintegral_t_fixed F hφ measurable_id' measurable_id' (NumberField.Idele.idelicHaar F) x
  have hu := (lintegral_eq_zero_iff' hmu.aemeasurable).1 hx0
  filter_upwards [hu] with u hu0
  have hmt : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k, N'.indicator 1 (iwPt F x u t k) * wt F t ∂(maximalCompactHaar F) :=
    measurable_lintegral_k_fixed F hφ measurable_id' x u
  have ht := (lintegral_eq_zero_iff' hmt.aemeasurable).1 hu0
  filter_upwards [ht] with t ht0
  have hkm : Measurable fun k : adelicMaximalCompact F => N'.indicator 1 (iwPt F x u t k) * wt F t :=
    measurable_integrand_fixed F hφ x u t
  have hk := (lintegral_eq_zero_iff' hkm.aemeasurable).1 ht0
  filter_upwards [hk] with k hk0
  intro hmem
  have h1 : N'.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (iwPt F x u t k) = 1 := by
    rw [Set.indicator_of_mem (hNN' hmem)]; rfl
  have h2 : N'.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (iwPt F x u t k) * wt F t = 0 := hk0
  rw [h1, one_mul] at h2
  exact wt_ne_zero F t h2

private theorem lintegral_out_eq_setLIntegral {S : Set (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) = ∫⁻ g in S, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  obtain ⟨hle, hcount, hTm, hT, hTint⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  obtain ⟨hHaar, hRight⟩ := isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F
  haveI := hcount
  haveI := hHaar
  haveI := hRight
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := sigmaFinite_adelicGLHaar F
  have h := HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out (adelicGLHaar (Fin 2) (𝓞 F) F)
    (rationalTorusUnipotent F) (isClosed_rationalTorusUnipotent F) (rationalTorusUnipotentHaar F) _ hle f hf
    (fun γ hγ g => hfH γ (hle hγ) g) S hS _ hT

  have hT1 := hTint (fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [setLIntegral_one, Measure.smul_apply, smul_eq_mul] at hT1
  rw [ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne] at hT1
  refine Eq.trans ?_ h.symm
  refine lintegral_congr fun q => ?_
  rw [setLIntegral_congr_fun hTm fun x _ => hfH (x : AdelicGL2 (𝓞 F) F) x.2 q.out, setLIntegral_const, hT1, mul_one]

private abbrev integrand (Φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ)
    (k : adelicMaximalCompact F) : ℝ≥0∞ :=
  Φ (iwPt F x u t k) * wt F t

private theorem mul_tsum_indicator_eq_tsum_integrand (S' : Set (AdelicGL2 (𝓞 F) F)) {f : AdelicGL2 (𝓞 F) F → ℝ≥0∞}
    (hfH : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g)
    (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    f (centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * wt F t *
        ∑' γ : (borelSubgroup F).map (globalPoints (𝓞 F) F),
          S'.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : AdelicGL2 (𝓞 F) F)⁻¹ * iwPt F x u t k) =
      ∑' i : Idx F, integrand F (S'.indicator f)
        (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x)) (i.1⁻¹ • u)
        (i.2.1⁻¹ • t) k := by
  rw [← ENNReal.tsum_mul_left, ← (coordEquiv F).tsum_eq]
  refine tsum_congr fun i => ?_
  rw [coordEquiv_apply_coe]
  have hwt : wt F (i.2.1⁻¹ • t) = wt F t := by
    rw [Subgroup.smul_def, smul_eq_mul]
    exact wt_mul_of_mem_principalIdeles F (i.2.1⁻¹).2 t
  have hf' : f ((coordElt F i)⁻¹ * iwPt F x u t k) =
      f (centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) := by
    rw [hfH _ ((rationalTorusUnipotent F).inv_mem (coordElt_mem_rationalTorusUnipotent F i)),
      apply_iwPt_of_invariant F hfH]
  simp only [integrand]
  rw [← coordElt_inv_mul_iwPt, hwt]
  by_cases hmem : (coordElt F i)⁻¹ * iwPt F x u t k ∈ S'
  · simp only [Set.indicator_of_mem hmem, hf', mul_one]
  · simp only [Set.indicator_of_notMem hmem, mul_zero, zero_mul]

private theorem
tsum_setLIntegral_adelicBox_dilate (s : M4aHerbrand.principalIdeles (𝓞 F) F) (Ξ : AdeleRing (𝓞 F) F → ℝ≥0∞) :
    ∑' β : AdeleRing.principalSubgroup (𝓞 F) F, ∫⁻ x in adelicBox F,
        Ξ (((s : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-β) +ᵥ x)) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ x, Ξ x ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := countable_principalSubgroup F
  have hbox := isAddFundamentalDomain_adelicBox F (adelicAddHaar (𝓞 F) F)
  rw [← hbox.lintegral_eq_tsum' fun y => Ξ (((s : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • y)]
  exact lintegral_smul_adelicAddHaar_of_distribHaarChar_eq_one F
    (distribHaarChar_eq_one_of_mem_principalIdeles F ((M4aHerbrand.principalIdeles (𝓞 F) F).inv_mem s.2)) Ξ

private theorem lintegral_out_eq_mul_of_isFundamentalDomain {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F))
    {S : Set (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F))
    {D D' : Set (AdeleRing (𝓞 F) F)ˣ}
    (hFD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hFD' : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
      (c * adelicAddHaar (𝓞 F) F (adelicBox F)) * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  haveI := sigmaFinite_idelicHaar F
  haveI := countable_principalIdeles F
  haveI := countable_idx F
  haveI : Countable ((borelSubgroup F).map (globalPoints (𝓞 F) F)) :=
    (isFundamentalDomain_boxSheet_rationalTorusUnipotent F).2.1

  have hS'ex := hS.nullMeasurableSet.exists_measurable_subset_ae_eq
  obtain ⟨S', -, hS'm, hS'ae⟩ := hS'ex
  have hΦ : Measurable (S'.indicator f) := hf.indicator hS'm

  have hgroup : ∫⁻ g, S'.indicator f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k, integrand F (S'.indicator f) x u t k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) := hc _ hΦ

  have hpart : ∀ᵐ x ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)),
      ∀ᵐ u ∂((NumberField.Idele.idelicHaar F).restrict D), ∀ᵐ t ∂((NumberField.Idele.idelicHaar F).restrict D'),
      ∀ᵐ k ∂(maximalCompactHaar F),
        ∑' γ : (borelSubgroup F).map (globalPoints (𝓞 F) F),
          S'.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : AdelicGL2 (𝓞 F) F)⁻¹ * iwPt F x u t k) = 1 := by
    have hN : adelicGLHaar (Fin 2) (𝓞 F) F {g | ¬ ∑' γ : (borelSubgroup F).map (globalPoints (𝓞 F) F),
        S'.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : AdelicGL2 (𝓞 F) F)⁻¹ * g) = 1} = 0 :=
      ae_iff.1 (ae_tsum_indicator_inv_mul_eq_one F hS hS'ae)
    have h := ae_iwPt_notMem_of_measure_eq_zero F hc0 hc hN
    refine ae_restrict_of_ae (h.mono fun x hx => ae_restrict_of_ae (hx.mono fun u hu => ae_restrict_of_ae
      (hu.mono fun t ht => ht.mono fun k hk => ?_)))
    simpa using hk

  set R : ℝ≥0∞ := ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
      f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
      ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) with hRdef
  clear_value R
  have hbox : adelicAddHaar (𝓞 F) F (adelicBox F) * R =
      ∫⁻ x in adelicBox F, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k,
          ∑' i : Idx F, integrand F (S'.indicator f)
            (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x)) (i.1⁻¹ • u)
            (i.2.1⁻¹ • t) k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) := by
    rw [mul_comm (adelicAddHaar (𝓞 F) F (adelicBox F)) R, ← setLIntegral_const (adelicBox F) R]
    refine lintegral_congr_ae (hpart.mono fun x hx => ?_)
    rw [hRdef]
    refine lintegral_congr_ae (hx.mono fun u hu => ?_)
    refine lintegral_congr_ae (hu.mono fun t ht => ?_)
    refine lintegral_congr_ae (ht.mono fun k hk => ?_)
    beta_reduce
    rw [← mul_tsum_indicator_eq_tsum_integrand F S' hfH x u t k, hk, mul_one]

  have hout : ∫⁻ x in adelicBox F, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k,
          ∑' i : Idx F, integrand F (S'.indicator f)
            (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x)) (i.1⁻¹ • u)
            (i.2.1⁻¹ • t) k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) =
      ∑' i : Idx F, ∫⁻ x in adelicBox F, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k, integrand F (S'.indicator f)
            (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x)) (i.1⁻¹ • u)
            (i.2.1⁻¹ • t) k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) := by
    have h1 : ∀ i : Idx F, Measurable fun x : AdeleRing (𝓞 F) F => ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k,
        integrand F (S'.indicator f) (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x))
          (i.1⁻¹ • u) (i.2.1⁻¹ • t) k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := fun i =>
      measurable_lintegral_u F hΦ (measurable_dilate_translate F ((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹) i.2.2)
        (measurable_subgroup_smul F _ i.1⁻¹) (measurable_subgroup_smul F _ i.2.1⁻¹)
        ((NumberField.Idele.idelicHaar F).restrict D) ((NumberField.Idele.idelicHaar F).restrict D')
    rw [← lintegral_tsum fun i => (h1 i).aemeasurable]
    refine lintegral_congr fun x => ?_
    have h2 : ∀ i : Idx F, Measurable fun u : (AdeleRing (𝓞 F) F)ˣ => ∫⁻ t in D', ∫⁻ k,
        integrand F (S'.indicator f) (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x))
          (i.1⁻¹ • u) (i.2.1⁻¹ • t) k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) := fun i =>
      measurable_lintegral_t_fixed F hΦ (measurable_subgroup_smul F _ i.1⁻¹) (measurable_subgroup_smul F _ i.2.1⁻¹)
        ((NumberField.Idele.idelicHaar F).restrict D') _
    rw [← lintegral_tsum fun i => (h2 i).aemeasurable]
    refine lintegral_congr fun u => ?_
    have h3 : ∀ i : Idx F, Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ∫⁻ k,
        integrand F (S'.indicator f) (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x))
          (i.1⁻¹ • u) (i.2.1⁻¹ • t) k ∂(maximalCompactHaar F) := fun i =>
      measurable_lintegral_k_fixed F hΦ (measurable_subgroup_smul F _ i.2.1⁻¹) _ _
    rw [← lintegral_tsum fun i => (h3 i).aemeasurable]
    refine lintegral_congr fun t => ?_
    have h4 : ∀ i : Idx F, Measurable fun k : adelicMaximalCompact F =>
        integrand F (S'.indicator f) (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x))
          (i.1⁻¹ • u) (i.2.1⁻¹ • t) k := fun i =>
      measurable_integrand_fixed F hΦ _ _ _
    rw [← lintegral_tsum fun i => (h4 i).aemeasurable]

  have hfold : ∑' i : Idx F, ∫⁻ x in adelicBox F, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k, integrand F (S'.indicator f)
            (((i.2.1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-i.2.2) +ᵥ x)) (i.1⁻¹ • u)
            (i.2.1⁻¹ • t) k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k, integrand F (S'.indicator f) x u t k
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_prod']

    have hβ : ∀ (d s : M4aHerbrand.principalIdeles (𝓞 F) F),
        (∑' β : AdeleRing.principalSubgroup (𝓞 F) F, ∫⁻ x in adelicBox F, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k,
            integrand F (S'.indicator f) (((s : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) • ((-β) +ᵥ x))
              (d⁻¹ • u) (s⁻¹ • t) k
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F)) =
        ∫⁻ x, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k, integrand F (S'.indicator f) x (d⁻¹ • u) (s⁻¹ • t) k
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F) := fun d s =>
      tsum_setLIntegral_adelicBox_dilate F s fun y => ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k,
        integrand F (S'.indicator f) y (d⁻¹ • u) (s⁻¹ • t) k
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
    simp_rw [hβ]

    have hs : ∀ d : M4aHerbrand.principalIdeles (𝓞 F) F,
        (∑' s : M4aHerbrand.principalIdeles (𝓞 F) F, ∫⁻ x, ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k,
            integrand F (S'.indicator f) x (d⁻¹ • u) (s⁻¹ • t) k
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F)) =
        ∫⁻ x, ∫⁻ u in D, ∫⁻ t, ∫⁻ k, integrand F (S'.indicator f) x (d⁻¹ • u) t k
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F) := by
      intro d
      rw [← lintegral_tsum fun s => (measurable_lintegral_u F hΦ measurable_id' (measurable_subgroup_smul F _ d⁻¹)
        (measurable_subgroup_smul F _ s⁻¹) _ _).aemeasurable]
      refine lintegral_congr fun x => ?_
      rw [← lintegral_tsum fun s => (measurable_lintegral_t_fixed F hΦ (measurable_subgroup_smul F _ d⁻¹)
        (measurable_subgroup_smul F _ s⁻¹) _ x).aemeasurable]
      refine lintegral_congr fun u => ?_
      exact (hFD'.lintegral_eq_tsum' fun t => ∫⁻ k, integrand F (S'.indicator f) x (d⁻¹ • u) t k
        ∂(maximalCompactHaar F)).symm
    simp_rw [hs]
    have hdm : ∀ d : M4aHerbrand.principalIdeles (𝓞 F) F, Measurable fun x : AdeleRing (𝓞 F) F =>
        ∫⁻ u in D, ∫⁻ t, ∫⁻ k, integrand F (S'.indicator f) x (d⁻¹ • u) t k
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := fun d =>
      measurable_lintegral_u F hΦ measurable_id' (measurable_subgroup_smul F _ d⁻¹) measurable_id' _ _
    rw [← lintegral_tsum fun d => (hdm d).aemeasurable]
    refine lintegral_congr fun x => ?_
    exact (hFD.lintegral_eq_tsum' fun u => ∫⁻ t, ∫⁻ k, integrand F (S'.indicator f) x u t k
      ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)).symm

  calc ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F)
      = ∫⁻ g in S, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_out_eq_setLIntegral F hS f hf hfH
    _ = ∫⁻ g, S'.indicator f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [← setLIntegral_congr hS'ae, lintegral_indicator hS'm]
    _ = c * (adelicAddHaar (𝓞 F) F (adelicBox F) * R) := by rw [hgroup, hbox, hout, hfold]
    _ = (c * adelicAddHaar (𝓞 F) F (adelicBox F)) * R := (mul_assoc _ _ _).symm

private theorem
lintegral_out_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F))
    {D D' : Set (AdeleRing (𝓞 F) F)ˣ}
    (hFD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hFD' : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
      (c * adelicAddHaar (𝓞 F) F (adelicBox F)) * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  obtain ⟨S, hS⟩ := exists_isFundamentalDomain_borelImage F
  exact lintegral_out_eq_mul_of_isFundamentalDomain F hc0 hc hS hFD hFD' f hf hfH

end IwasawaQuotientDisintegration
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm
open scoped ENNReal ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace ParsevalAboveFloor

variable (F : Type) [Field F] [NumberField F]

private def normChar : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

private theorem normChar_apply (x : (AdeleRing (𝓞 F) F)ˣ) : ((normChar F x : ℝˣ) : ℝ) = ideleNorm F x :=
  rfl

variable {F}

section Measurability

variable [SecondCountableTopology (AdelicGL2 (𝓞 F) F)] [SFinite (adelicAddHaar (𝓞 F) F)]

private theorem measurable_weylIntertwiningIntegral {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : Measurable h) :
    Measurable (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) h) := by
  have hc : Continuous fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F =>
      (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 p.2 * p.1 :=
    (continuous_const.mul (continuous_unipotentGL2.comp continuous_snd)).mul continuous_fst
  have hsm : StronglyMeasurable fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F =>
      h ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 p.2 * p.1) := (hh.comp hc.measurable).stronglyMeasurable
  show Measurable fun g : AdelicGL2 (𝓞 F) F =>
    ∫ x, h ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ∂(adelicAddHaar (𝓞 F) F)
  exact (hsm.integral_prod_right' (ν := adelicAddHaar (𝓞 F) F)).measurable

private theorem measurable_weylIntertwiningIntegral_family {h : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => h p.1 p.2) {s : ℝ → ℂ} (hs : Continuous s) :
    Measurable fun p : ℝ × adelicMaximalCompact F =>
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (h (s p.1)) (p.2 : AdelicGL2 (𝓞 F) F) := by
  have hc : Continuous fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F =>
      (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 p.2 * p.1 :=
    (continuous_const.mul (continuous_unipotentGL2.comp continuous_snd)).mul continuous_fst
  have hπ₂ : Measurable fun q : (ℝ × adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      ((q.1.2 : AdelicGL2 (𝓞 F) F), q.2) :=
    ((measurable_subtype_val_adelicMaximalCompact F).comp measurable_fst.snd).prodMk measurable_snd
  have hW := hc.measurable.comp hπ₂
  have ht : Measurable fun q : (ℝ × adelicMaximalCompact F) × AdeleRing (𝓞 F) F => s q.1.1 :=
    hs.measurable.comp measurable_fst.fst
  have hsm := (hjc.measurable.comp (ht.prodMk hW)).stronglyMeasurable
  show Measurable fun p : ℝ × adelicMaximalCompact F =>
    ∫ x, h (s p.1) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (p.2 : AdelicGL2 (𝓞 F) F)) ∂(adelicAddHaar (𝓞 F) F)
  exact (hsm.integral_prod_right' (ν := adelicAddHaar (𝓞 F) F)).measurable

end Measurability
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

private theorem const_mul_const_mul (cQ V L : ℝ) :
    ((cQ * (V * (L / 2)) : ℝ) : ℂ) * (((V * (2 * Real.pi)) : ℝ) : ℂ) *
        ((((4 * Real.pi)⁻¹ : ℝ) : ℂ) * conj (((4 * Real.pi)⁻¹ : ℝ) : ℂ)) =
      (cQ * V ^ 2 * L / (16 * Real.pi) : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.conj_ofReal]
  push_cast
  field_simp
  ring

private theorem integral_integral_const_mul_mul_conj {K : Type*} [MeasurableSpace K] (m : Measure K) (κ : ℂ)
    (f g : ℝ → K → ℂ) :
    ∫ τ : ℝ, ∫ k, κ * f τ k * conj (κ * g τ k) ∂m = κ * conj κ * ∫ τ : ℝ, ∫ k, f τ k * conj (g τ k) ∂m := by
  have h : ∀ τ k, κ * f τ k * conj (κ * g τ k) = κ * conj κ * (f τ k * conj (g τ k)) := fun τ k => by
    rw [map_mul]; ring
  simp_rw [h, integral_const_mul]

variable [SecondCountableTopology (AdelicGL2 (𝓞 F) F)] [SFinite (adelicAddHaar (𝓞 F) F)]
  [SFinite (NumberField.Idele.idelicHaar F)]

private theorem setIntegral_quotient_slab_eq

    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (A : ℝ)

    {cQ : ℝ≥0∞} (hcQ : cQ ≠ ∞) {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hdis : IwasawaBochner.HasIwasawaDisintegration F cQ D D)
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F)) (hnorm : Measurable (ideleNorm F))
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hC : IsCompact (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)))

    {ι : Type} [Fintype ι] (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
    (hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
    (hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
    {ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ} (hμν : ∀ e x, μ e x * ν e x = ξ x)
    (r : ι → ι) (hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
    (hdist : ∀ e e', e ≠ e' → ∃ x ∈ normOneIdeles F, μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)

    (hα : ∀ x, 0 < ((normChar F x : ℝˣ) : ℝ)) (hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) (normChar F))
    (φf ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) (normChar F) hα s) (etaSnd (ν e) (normChar F) hα s)
      (φf e s))
    (hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) (normChar F) hα s) (etaSnd (ν e) (normChar F) hα s)
      (ψf e s))
    (hφjc : ∀ e, Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => φf e p.1 p.2)
    (hψjc : ∀ e, Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)
    (hφhol : ∀ e g, Differentiable ℂ fun s => φf e s g)
    (hφdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
        ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    (hψdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
        ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ (t : ℝ), ∀ g ∈ C, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)

    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, φ (x * g) = φ g)
    (hψinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, ψ (x * g) = ψ g)
    (hφcen : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * φ g)
    (hψcen : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      ψ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * ψ g)
    (hφrep : ∀ σ' : ℝ, ∀ g, φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
    (hψrep : ∀ σ' : ℝ, ∀ g, ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
    (σ : ℝ) (hσ : 1 / 2 < σ)

    (hMrep : ∀ g, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g =
      ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ,
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e ((σ : ℂ) + (t : ℂ) * Complex.I)) g)
    (hMind : ∀ (e : ι) (s : ℂ), IsInducedSection (𝓞 F) F (etaFst (ν e) (normChar F) hα (-s))
      (etaSnd (μ e) (normChar F) hα (-s)) (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s)))
    (hMbd : ∀ (e : ι) (m : ℝ → ℝ),
      (∀ t : ℝ, ∀ g ∈ adelicMaximalCompact F, ‖ψf e ((σ : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ t : ℝ, ∀ k ∈ adelicMaximalCompact F,
        ‖weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e ((σ : ℂ) + (t : ℂ) * Complex.I)) k‖ ≤
          Kc * m t) :
    ∫ q in {q : RationalTorusUnipotentQuotient F |
        ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂},
      φ q.out * conj (ψ q.out + (A : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      (cQ.toReal * V.toReal ^ 2 * Real.log (d₂ / d₁) / (16 * Real.pi) : ℂ) *
        ∑ e, ∫ t : ℝ,
          ((∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
              conj (ψf e (-(σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) +
            (A : ℂ)⁻¹ *
              ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
                conj (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
                  (ψf (r e) ((σ : ℂ) - (t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) := by
  classical

  rcases isEmpty_or_nonempty ι with _ | hne
  · have hφ0 : ∀ g, φ g = 0 := fun g => by rw [hφrep σ g]; exact Finset.sum_of_isEmpty _
    simp [hφ0]

  set κ : ℂ := (((4 * Real.pi)⁻¹ : ℝ) : ℂ) with hκ
  have hκu : IsUnit (κ * conj κ) := by
    rw [hκ, Complex.conj_ofReal, isUnit_iff_ne_zero]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (by positivity)))
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (by positivity)))
  have hσ0 : 0 < σ := lt_trans one_half_pos hσ
  have hαn : ∀ x, ((normChar F x : ℝˣ) : ℝ) = ideleNorm F x := normChar_apply F
  have hξ : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1 := fun z => EisensteinTorusFacts.norm_xi_eq_one hμν hμ hν hne.some z
  have hdistμ : ∀ e e', e ≠ e' → ∃ x ∈ normOneIdeles F, μ e x ≠ μ e' x :=
    EisensteinTorusFacts.exists_apply_ne_of_mul_eq hμν hdist
  have hrinv : Function.Involutive r :=
    EisensteinTorusFacts.involutive_of_swap (μ := fun e => ⇑(μ e)) (ν := fun e => ⇑(ν e))
      (fun e => ⟨congrArg DFunLike.coe (hr e).1, congrArg DFunLike.coe (hr e).2⟩)
      (EisensteinTorusFacts.ne_or_ne_of_exists hdist)
  have hι : Continuous fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F) := continuous_subtype_val
  have hιC : ∀ k : adelicMaximalCompact F,
      (k : AdelicGL2 (𝓞 F) F) ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) := fun k => k.2

  set Mψ : AdelicGL2 (𝓞 F) F → ℂ := weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ
  have hMm : Measurable Mψ := measurable_weylIntertwiningIntegral hψm
  have hMinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Mψ (x * g) = Mψ g :=
    TorusExpansion.apply_mul_eq_of_sum
      (f := fun e s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s)) (σ' := σ) (κ := κ)
      hMrep (fun e τ => EisensteinTorusFacts.apply_mul_of_mem_of_isInducedSection
        (hMind e ((σ : ℂ) + (τ : ℂ) * Complex.I))
        (etaFst_isIdeleClassChar (hνic e) hprin _) (etaSnd_isIdeleClassChar (hμic e) hprin _))
  have hMcen : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      Mψ (centralScalar (𝓞 F) F z * g) = ((ξ z : ℂˣ) : ℂ) * Mψ g :=
    TorusExpansion.apply_centralScalar_mul_eq_of_sum
      (f := fun e s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s)) (σ' := σ) (κ := κ)
      hMrep (fun e τ z g => TorusExpansion.apply_centralScalar_mul_of_isInducedSection
        (fun z => by rw [TorusExpansion.etaFst_apply_mul_etaSnd_apply, mul_comm, hμν e z])
        (hMind e ((σ : ℂ) + (τ : ℂ) * Complex.I)) z g)

  set S : Set (AdelicGL2 (𝓞 F) F) :=
    {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} with hSdef
  have hTS : {q : RationalTorusUnipotentQuotient F |
      ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂} =
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S} := rfl
  rw [hTS]
  have hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S := fun x hx g => by
    rw [hSdef, Set.mem_setOf_eq, Set.mem_setOf_eq, EisensteinTorusFacts.ideleNorm_det_mul_eq_of_mem x hx g]
  have hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S} :=
    EisensteinTorusFacts.measurableSet_setOf_ideleNorm_det_out_mem_Icc d₁ d₂ hS
      (fun P hP hPinv => InvariantDescent.measurable_apply_out P hP hPinv)
  have hY : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      0 < ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) := fun t k =>
    EisensteinTorusFacts.ideleNorm_mul_ideleNorm_det_pos t _
  have hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        ideleNorm F z ∈ NormWindowVolume.window d₁ d₂
          (ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F))) :=
    fun z t k => EisensteinTorusFacts.iwasawa_mem_slab_iff d₁ d₂ z t _

  have hPφ : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      φ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        MellinParseval.lineProfile σ
          (SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ k)
          (ideleNorm F t) := fun t k =>
    TorusExpansion.apply_diagOne_mul_eq_sum (f := φf) (σ' := σ) (Φ := φ) (κ := κ) hαn (fun e τ => hφf e _)
      (hφrep σ) t _
  have hQψ : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      ψ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        MellinParseval.lineProfile (-σ)
          (SectionLineFamily.lineFamily (ψf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ
            (-σ) k)
          (ideleNorm F t) := fun t k =>
    TorusExpansion.apply_diagOne_mul_eq_sum (f := ψf) (σ' := -σ) (Φ := ψ) (κ := κ) hαn (fun e τ => hψf e _)
      (hψrep (-σ)) t _

  set bM : ι → adelicMaximalCompact F → ℝ → ℂ := fun e k u =>
    κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
      (ψf (r e) (-((((-σ : ℝ)) : ℂ) + (u : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 F) F) with hbM
  have hMrep' : ∀ g, Mψ g = ∑ e, κ * ∫ τ : ℝ,
      (fun e (w : ℂ) => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e (-w))) e
        (((-σ : ℝ) : ℂ) + (τ : ℂ) * Complex.I) g := fun g => by
    rw [hMrep g]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    congr 1
    rw [← integral_neg_eq_self
      (fun τ : ℝ => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
        (ψf e ((σ : ℂ) + (τ : ℂ) * Complex.I)) g) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    show weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e ((σ : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I)) g =
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
        (ψf e (-(((-σ : ℝ) : ℂ) + (τ : ℂ) * Complex.I))) g
    have hs : (σ : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I = -(((-σ : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hs]
  have hQM : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Mψ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ∑ e, ((μ e t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        MellinParseval.lineProfile (-σ) (bM e k) (ideleNorm F t) := fun t k => by
    rw [TorusExpansion.apply_diagOne_mul_eq_sum
      (f := fun e (w : ℂ) => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e (-w)))
      (σ' := -σ) (Φ := Mψ) (κ := κ) (χ := ν) (χ' := μ) hαn
      (fun e τ => by simpa only [neg_neg] using hMind e (-(((-σ : ℝ) : ℂ) + (τ : ℂ) * Complex.I))) hMrep' t _,
      ← Equiv.sum_comp (hrinv.toPerm r)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [Function.Involutive.coe_toPerm, (hr e).2, hbM]

  have ha : ∀ (e : ι) (k : adelicMaximalCompact F), Integrable
      (SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ k) :=
    fun e k => SectionLineFamily.integrable_lineFamily (hφjc e) (hφdec e) hC hιC κ σ k
  have hac : ∀ (e : ι) (k : adelicMaximalCompact F), Continuous
      (SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ k) :=
    fun e k => SectionLineFamily.continuous_lineFamily (hφjc e) κ σ k
  have hap : ∀ (e : ι) (k : adelicMaximalCompact F), MellinParseval.HasIntegrableProfile σ
      (SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ k) :=
    fun e k => SectionLineFamily.hasIntegrableProfile_lineFamily (hφhol e) (hφdec e) hC hιC κ σ k
  have hb₁ : ∀ (e : ι) (k : adelicMaximalCompact F), Integrable
      (SectionLineFamily.lineFamily (ψf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ (-σ)
        k) :=
    fun e k => SectionLineFamily.integrable_lineFamily (hψjc e) (hψdec e) hC hιC κ (-σ) k
  have hbm₁ : ∀ e : ι, Measurable fun p : ℝ × adelicMaximalCompact F =>
      SectionLineFamily.lineFamily (ψf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ (-σ)
        p.2 p.1 := fun e =>
    (SectionLineFamily.measurable_lineFamily_prod (hψjc e) hι κ (-σ)).comp
      ((measurable_fst.prodMk measurable_snd).prodMk measurable_fst)
  have hbd₁ : ∀ e : ι, ∃ mb : ℝ → ℝ, Integrable mb ∧ (∃ B : ℝ, ∀ u, mb u ≤ B) ∧
      ∀ (u : ℝ) (k : adelicMaximalCompact F),
        ‖SectionLineFamily.lineFamily (ψf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ (-σ)
          k u‖ ≤ mb u := fun e => by
    have hmaj := SectionLineFamily.exists_majorant (hψdec e) hC hιC κ (-σ) 1
    obtain ⟨m, hmi, ⟨B, hB⟩, hm⟩ := hmaj
    refine ⟨fun u => ‖κ‖ * m u, hmi.const_mul _, ⟨‖κ‖ * B, fun u => mul_le_mul_of_nonneg_left (hB u)
      (norm_nonneg κ)⟩, fun u k => ?_⟩
    exact hm (-σ) (by simp) k u

  have hbm₂ : ∀ e : ι, Measurable fun p : ℝ × adelicMaximalCompact F => bM e p.2 p.1 := fun e =>
    (measurable_weylIntertwiningIntegral_family (hψjc (r e))
      (s := fun u : ℝ => -(((-σ : ℝ) : ℂ) + (u : ℂ) * Complex.I))
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg)).const_mul κ
  have hbd₂ : ∀ e : ι, ∃ mb : ℝ → ℝ, Integrable mb ∧ (∃ B : ℝ, ∀ u, mb u ≤ B) ∧
      ∀ (u : ℝ) (k : adelicMaximalCompact F), ‖bM e k u‖ ≤ mb u := fun e => by
    have hmaj := hψdec (r e) σ _ hC
    obtain ⟨m, hmi, ⟨B, hB⟩, hm⟩ := hmaj
    have hKex := hMbd (r e) m (fun t g hg => hm σ (le_of_eq (abs_of_pos hσ0)) t g hg)
    obtain ⟨Kc, hKc0, hKc⟩ := hKex
    refine ⟨fun u => ‖κ‖ * (Kc * m (-u)), (hmi.comp_neg.const_mul Kc).const_mul _,
      ⟨‖κ‖ * (Kc * B), fun u => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB (-u)) hKc0)
        (norm_nonneg κ)⟩, fun u k => ?_⟩
    rw [hbM]
    show ‖κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
      (ψf (r e) (-(((-σ : ℝ) : ℂ) + (u : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 F) F)‖ ≤ ‖κ‖ * (Kc * m (-u))
    have hs : -(((-σ : ℝ) : ℂ) + (u : ℂ) * Complex.I) = (σ : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [norm_mul, hs]
    exact mul_le_mul_of_nonneg_left (hKc (-u) _ k.2) (norm_nonneg κ)
  have hb₂ : ∀ (e : ι) (k : adelicMaximalCompact F), Integrable (bM e k) := fun e k => by
    obtain ⟨mb, hmbi, -, hmb⟩ := hbd₂ e
    exact hmbi.mono' ((hbm₂ e).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => hmb u k)

  have hL₁ : ∀ e e' : ι, Integrable (fun p : ℝ × adelicMaximalCompact F => ((p.1⁻¹ : ℝ) : ℂ) *
      (MellinParseval.lineProfile σ (SectionLineFamily.lineFamily (φf e)
          (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ p.2) p.1 *
        conj (MellinParseval.lineProfile (-σ) (SectionLineFamily.lineFamily (ψf e')
          (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ (-σ) p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (maximalCompactHaar F)) := fun e e' =>
    SectionLineFamily.integrable_inv_mul_lineProfile_mul_conj_lineProfile (hφjc e) (hφhol e) (hφdec e) hC hι hιC
      κ σ (add_neg_cancel σ) (hbm₁ e') (hbd₁ e') (maximalCompactHaar F)
  have hL₂ : ∀ e e' : ι, Integrable (fun p : ℝ × adelicMaximalCompact F => ((p.1⁻¹ : ℝ) : ℂ) *
      (MellinParseval.lineProfile σ (SectionLineFamily.lineFamily (φf e)
          (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ p.2) p.1 *
        conj (MellinParseval.lineProfile (-σ) (bM e' p.2) p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (maximalCompactHaar F)) := fun e e' =>
    SectionLineFamily.integrable_inv_mul_lineProfile_mul_conj_lineProfile (hφjc e) (hφhol e) (hφdec e) hC hι hιC
      κ σ (add_neg_cancel σ) (hbm₂ e') (hbd₂ e') (maximalCompactHaar F)
  have hint₁ : ∀ e : ι, Integrable (fun p : ℝ × adelicMaximalCompact F =>
      SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ p.2
          p.1 *
        conj (SectionLineFamily.lineFamily (ψf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ
          (-σ) p.2 p.1))
      (volume.prod (maximalCompactHaar F)) := fun e =>
    SectionLineFamily.integrable_lineFamily_mul_conj (hφjc e) (hφdec e) hC hι hιC κ σ (hbm₁ e) (hbd₁ e)
      (maximalCompactHaar F)
  have hint₂ : ∀ e : ι, Integrable (fun p : ℝ × adelicMaximalCompact F =>
      SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ p.2
          p.1 * conj (bM e p.2 p.1))
      (volume.prod (maximalCompactHaar F)) := fun e =>
    SectionLineFamily.integrable_lineFamily_mul_conj (hφjc e) (hφdec e) hC hι hιC κ σ (hbm₂ e) (hbd₂ e)
      (maximalCompactHaar F)

  have hdk : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F) :=
    ((IwasawaQuotientDisintegration.continuous_diagOne F).measurable.comp measurable_fst).mul
      ((measurable_subtype_val_adelicMaximalCompact F).comp measurable_snd)
  have hHm : ∀ {Φ₂ : AdelicGL2 (𝓞 F) F → ℂ}, Measurable Φ₂ → AEStronglyMeasurable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * conj (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      (((NumberField.Idele.idelicHaar F).restrict D).prod (maximalCompactHaar F)) := fun hΦ₂m =>
    ((hφm.comp hdk).mul (Complex.continuous_conj.measurable.comp (hΦ₂m.comp hdk))).aestronglyMeasurable
  have hLam : ∀ e : ι, StronglyMeasurable fun p : ℝ × adelicMaximalCompact F =>
      MellinParseval.lineProfile σ (SectionLineFamily.lineFamily (φf e)
        (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ p.2) p.1 := fun e =>
    SectionLineFamily.stronglyMeasurable_lineProfile_lineFamily (hφjc e) hι κ σ σ
  have hLb₁m : ∀ e : ι, StronglyMeasurable fun p : ℝ × adelicMaximalCompact F =>
      MellinParseval.lineProfile (-σ) (SectionLineFamily.lineFamily (ψf e)
        (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ (-σ) p.2) p.1 := fun e =>
    SectionLineFamily.stronglyMeasurable_lineProfile_lineFamily (hψjc e) hι κ (-σ) (-σ)
  have hLb₂m : ∀ e : ι, StronglyMeasurable fun p : ℝ × adelicMaximalCompact F =>
      MellinParseval.lineProfile (-σ) (bM e p.2) p.1 := fun e =>
    SectionLineFamily.stronglyMeasurable_lineProfile_of_measurable (hbm₂ e) (-σ)
  have hintψ := TorusExpansion.integrable_mul_conj_withDensity_prod hnorm hV hVT (maximalCompactHaar F) hμ hμ
    (gk := fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) (hHm hψm)
    (L₁ := fun e k => MellinParseval.lineProfile σ
      (SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ k))
    (L₂ := fun e k => MellinParseval.lineProfile (-σ)
      (SectionLineFamily.lineFamily (ψf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ (-σ) k))
    hPφ hQψ hLam hLb₁m hL₁
  have hintM := TorusExpansion.integrable_mul_conj_withDensity_prod hnorm hV hVT (maximalCompactHaar F) hμ hμ
    (gk := fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) (hHm hMm)
    (L₁ := fun e k => MellinParseval.lineProfile σ
      (SectionLineFamily.lineFamily (φf e) (fun k : adelicMaximalCompact F => (k : AdelicGL2 (𝓞 F) F)) κ σ k))
    (L₂ := fun e k => MellinParseval.lineProfile (-σ) (bM e k)) hPφ hQM hLam hLb₂m hL₂

  have hI₁ := SlabToTorus.integrableOn_mul_conj_apply_out hdis hcQ hπ hnorm hV hVT hd₁ hd.le hS hT hSinv hY hSco
    φ ψ hφm hψm hφinv hψinv (fun z t k => EisensteinTorusFacts.mul_conj_apply_iwasawa hξ hφcen hψcen z t k)
    hintψ
  have hI₂ := SlabToTorus.integrableOn_mul_conj_apply_out hdis hcQ hπ hnorm hV hVT hd₁ hd.le hS hT hSinv hY hSco
    φ Mψ hφm hMm hφinv hMinv (fun z t k => EisensteinTorusFacts.mul_conj_apply_iwasawa hξ hφcen hMcen z t k) hintM
  have hsplit : ∀ q : RationalTorusUnipotentQuotient F,
      φ q.out * conj (ψ q.out + (A : ℂ)⁻¹ * Mψ q.out) =
        φ q.out * conj (ψ q.out) + (A : ℂ)⁻¹ * (φ q.out * conj (Mψ q.out)) := fun q => by
    rw [map_add, map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  simp_rw [hsplit]
  rw [integral_add hI₁ (Integrable.const_mul hI₂ _), integral_const_mul]

  rw [SlabToTorus.setIntegral_mul_conj_apply_out_eq_mul_setIntegral hdis hπ hnorm hV hVT hd₁ hd.le hS hT hSinv hY
      hSco φ ψ hφm hψm hφinv hψinv (fun z t k => EisensteinTorusFacts.mul_conj_apply_iwasawa hξ hφcen hψcen z t k)
      hintψ,
    SlabToTorus.setIntegral_mul_conj_apply_out_eq_mul_setIntegral hdis hπ hnorm hV hVT hd₁ hd.le hS hT hSinv hY
      hSco φ Mψ hφm hMm hφinv hMinv (fun z t k => EisensteinTorusFacts.mul_conj_apply_iwasawa hξ hφcen hMcen z t k)
      hintM]

  rw [TorusPairing.setIntegral_inv_smul_integral_mul_conj_eq_mul_sum hDF hV hVT μ hμ hμic
      (fun e => (hμc e).measurable) hdistμ σ _ _ ha hac hap hb₁ hL₁ hint₁ _ _ hPφ hQψ,
    TorusPairing.setIntegral_inv_smul_integral_mul_conj_eq_mul_sum hDF hV hVT μ hμ hμic
      (fun e => (hμc e).measurable) hdistμ σ _ _ ha hac hap hb₂ hL₂ hint₂ _ _ hPφ hQM]

  have hneg : ∀ t : ℝ, -(-(σ : ℂ) + (t : ℂ) * Complex.I) = (σ : ℂ) - (t : ℂ) * Complex.I := fun t => by ring
  simp only [SectionLineFamily.lineFamily_apply, hbM]
  simp_rw [integral_integral_const_mul_mul_conj, Complex.ofReal_neg, hneg, ← Finset.mul_sum]

  have hconjκ : ∀ a b : ℂ, κ * a * (conj κ * b) = κ * conj κ * (a * b) := fun a b => by ring
  have hX : ∀ e : ι, Integrable fun t : ℝ => ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
      conj (ψf e (-(σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F) := fun e => by
    have h := (hint₁ e).integral_prod_left
    simp only [SectionLineFamily.lineFamily_apply, map_mul, hconjκ, integral_const_mul, Complex.ofReal_neg] at h
    exact (integrable_const_mul_iff hκu _).1 h
  have hYint : ∀ e : ι, Integrable fun t : ℝ => ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
      conj (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf (r e) ((σ : ℂ) - (t : ℂ) * Complex.I))
        (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F) := fun e => by
    have h := (hint₂ e).integral_prod_left
    simp only [SectionLineFamily.lineFamily_apply, hbM, map_mul, hconjκ, integral_const_mul, Complex.ofReal_neg,
      hneg] at h
    exact (integrable_const_mul_iff hκu _).1 h
  rw [Finset.sum_congr rfl fun e _ => integral_add (hX e) (Integrable.const_mul (hYint e) _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

  have hK := const_mul_const_mul cQ.toReal V.toReal (Real.log (d₂ / d₁))
  rw [← hκ] at hK
  linear_combination ((∑ e, ∫ t : ℝ, ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
      conj (ψf e (-(σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) +
    (A : ℂ)⁻¹ * ∑ e, ∫ t : ℝ, ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
      conj (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf (r e) ((σ : ℂ) - (t : ℂ) * Complex.I))
        (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) * hK

end ParsevalAboveFloor
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

section

open MeasureTheory

noncomputable section

namespace WeylLineInterchange

section Generic

variable {ι X G : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]

private theorem integral_sum_lineIntegral_comp (E : Finset ι) (κ : ℂ) (Ψ : ι → ℝ → G → ℂ) (T : X → G)
    (hΨ : ∀ e ∈ E, Integrable (fun p : ℝ × X => Ψ e p.1 (T p.2)) (volume.prod ν)) :
    ∫ x, (∑ e ∈ E, κ * ∫ t, Ψ e t (T x)) ∂ν = ∑ e ∈ E, κ * ∫ t, ∫ x, Ψ e t (T x) ∂ν := by
  refine (integral_finsetSum E fun e he => ?_).trans (Finset.sum_congr rfl fun e he => ?_)
  · exact ((hΨ e he).integral_prod_right).const_mul κ
  · rw [integral_const_mul]
    congr 1
    exact (integral_integral_swap (f := fun t x => Ψ e t (T x)) (hΨ e he)).symm

omit [SFinite ν] in

private theorem integrable_prod_of_majorant (f : ℝ → G → ℂ) (T : X → G)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × X => f p.1 (T p.2)) (volume.prod ν))
    (S : ℝ → ℝ) (hS : Integrable S) (M : X → ℝ) (hM : Integrable M ν)
    (hbound : ∀ t x, ‖f t (T x)‖ ≤ S t * M x) :
    Integrable (fun p : ℝ × X => f p.1 (T p.2)) (volume.prod ν) :=
  (hS.mul_prod hM).mono' hmeas (Filter.Eventually.of_forall fun p => hbound p.1 p.2)

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

section Intertwining

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [MeasurableSpace (NumberField.AdeleRing R K)]

open AutomorphicForm

private theorem
weylIntertwiningIntegral_sum_lineIntegral {ι : Type*} (ν : Measure (NumberField.AdeleRing R K)) [SFinite ν]
    (E : Finset ι) (κ : ℂ) (Ψ : ι → ℝ → AdelicGL2 R K → ℂ) (g : AdelicGL2 R K)
    (hΨ : ∀ e ∈ E, Integrable (fun p : ℝ × NumberField.AdeleRing R K =>
      Ψ e p.1 ((adelicWeyl R K)⁻¹ * unipotentGL2 p.2 * g)) (volume.prod ν)) :
    weylIntertwiningIntegral R K ν (fun g' => ∑ e ∈ E, κ * ∫ t, Ψ e t g') g
      = ∑ e ∈ E, κ * ∫ t, weylIntertwiningIntegral R K ν (Ψ e t) g := by
  unfold weylIntertwiningIntegral
  exact integral_sum_lineIntegral_comp E κ Ψ (fun x => (adelicWeyl R K)⁻¹ * unipotentGL2 x * g) hΨ

private theorem weylIntertwiningIntegral_sum_lineIntegral_of_majorant {ι : Type*}
    (ν : Measure (NumberField.AdeleRing R K)) [SFinite ν]
    (E : Finset ι) (κ : ℂ) (Ψ : ι → ℝ → AdelicGL2 R K → ℂ) (g : AdelicGL2 R K)
    (hmeas : ∀ e ∈ E, AEStronglyMeasurable (fun p : ℝ × NumberField.AdeleRing R K =>
      Ψ e p.1 ((adelicWeyl R K)⁻¹ * unipotentGL2 p.2 * g)) (volume.prod ν))
    (S : ι → ℝ → ℝ) (hS : ∀ e ∈ E, Integrable (S e))
    (M : NumberField.AdeleRing R K → ℝ) (hM : Integrable M ν)
    (hbound : ∀ e ∈ E, ∀ (t : ℝ) (x : NumberField.AdeleRing R K),
      ‖Ψ e t ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g)‖ ≤ S e t * M x) :
    weylIntertwiningIntegral R K ν (fun g' => ∑ e ∈ E, κ * ∫ t, Ψ e t g') g
      = ∑ e ∈ E, κ * ∫ t, weylIntertwiningIntegral R K ν (Ψ e t) g :=
  weylIntertwiningIntegral_sum_lineIntegral R K ν E κ Ψ g fun e he =>
    integrable_prod_of_majorant (Ψ e) (fun x => (adelicWeyl R K)⁻¹ * unipotentGL2 x * g) (hmeas e he)
      (S e) (hS e he) M hM (hbound e he)

end Intertwining
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

section KeyClose

open AutomorphicForm NumberField NumberField.AdelicHeight
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.AdeleRing.secondCountableTopology

variable (F : Type) [Field F] [NumberField F]

private theorem norm_etaSnd_apply_of_unitary {ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaSnd ν α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, norm_mul, hν x, one_mul, norm_cpowChar_apply, Complex.neg_re, re_add_half]

private theorem norm_mul_mul_norm_eq_of_isInducedSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) {s s' : ℂ} (hre : s.re = s'.re)
    {φ h : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hh : IsInducedSection (𝓞 F) F (etaFst 1 α hα s') (etaSnd 1 α hα s') h)
    {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    ‖φ (b * g)‖ * ‖h g‖ = ‖h (b * g)‖ * ‖φ g‖ := by
  have h1 : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp
  rw [hφ b hb g, hh b hb g]
  simp only [norm_mul]
  rw [norm_etaFst_apply_of_unitary hμ, norm_etaSnd_apply_of_unitary F hν, norm_etaFst_apply_of_unitary h1,
    norm_etaSnd_apply_of_unitary F h1, hre]
  ring

private theorem exists_mem_adelicBorel_mem_adelicMaximalCompact_weyl_inv_mul_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    ∃ b ∈ adelicBorel (𝓞 F) F, ∃ c ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)),
      (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x = b * c := by
  have hiw :=
    exists_mem_adelicBorel_mul_eq F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
  obtain ⟨b, k, hb, hkf, hka, hbk⟩ := hiw
  exact ⟨b, hb, k, (mem_adelicMaximalCompact_iff (K := F)).2 ⟨hkf, hka⟩, hbk⟩

private theorem weylIntertwiningIntegral_eq_sum_integral_weylIntertwiningIntegral :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hψdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (σ : ℝ) (_hσ : (1 / 2 : ℝ) < σ) (g : AdelicGL2 (𝓞 F) F),
    weylIntertwiningIntegral (𝓞 F) F (AdelicHaar.adelicAddHaar (𝓞 F) F) ψ g
      = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, weylIntertwiningIntegral (𝓞 F) F (AdelicHaar.adelicAddHaar (𝓞 F) F)
            (ψf e ((σ : ℂ) + (t : ℂ) * Complex.I)) g := by
  intro α hα ι _ μ ν hμ hν ψf hψf hψjc hψdec ψ hψrep σ hσ g
  have hψ : ψ = fun g' => ∑ e ∈ (Finset.univ : Finset ι), (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, ψf e ((σ : ℂ) + (t : ℂ) * Complex.I) g' := funext fun g' => hψrep σ g'

  have hsec₀ := isInducedSection_adelicHeight_cpow F
  obtain ⟨-, h1u, hsec⟩ := hsec₀
  set hσf : AdelicGL2 (𝓞 F) F → ℂ := fun y => ((adelicHeight F y : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) with hσf_def
  have hsecσ : IsInducedSection (𝓞 F) F (etaFst 1 α hα σ) (etaSnd 1 α hα σ) hσf := hsec hα σ
  have hHc : Continuous hσf :=
    (Complex.continuous_ofReal.comp (continuous_adelicHeight F)).cpow continuous_const
      fun y => Complex.ofReal_mem_slitPlane.2 (adelicHeight_pos y)
  have hHpos : ∀ y, 0 < ‖hσf y‖ := fun y => by
    rw [hσf_def]
    simp only []
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos y)]
    exact Real.rpow_pos_of_pos (adelicHeight_pos y) _
  have hMint : Integrable
      (fun x : AdeleRing (𝓞 F) F => ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)‖)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) :=
    (weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 h1u h1u (σ : ℂ) (by simpa using hσ) hσf
      hsecσ hHc g).norm

  set Cg : Set (AdelicGL2 (𝓞 F) F) := (fun c => c * g) '' (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))
    with hCg_def
  have hCg : IsCompact Cg := (isCompact_adelicMaximalCompact F).image (continuous_id.mul continuous_const)
  have hCg_ne : Cg.Nonempty := ⟨1 * g, 1, (adelicMaximalCompact F).one_mem, rfl⟩
  obtain ⟨y₀, -, hmin⟩ := hCg.exists_isMinOn hCg_ne hHc.norm.continuousOn
  have hc₀ : 0 < ‖hσf y₀‖ := hHpos y₀

  choose m hm using fun e => hψdec e |σ| Cg hCg
  rw [hψ]
  refine weylIntertwiningIntegral_sum_lineIntegral_of_majorant (𝓞 F) F (AdelicHaar.adelicAddHaar (𝓞 F) F)
    Finset.univ _ (fun e t => ψf e ((σ : ℂ) + (t : ℂ) * Complex.I)) g ?_ (fun e t => m e t * ‖hσf y₀‖⁻¹) ?_
    (fun x => ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)‖) hMint ?_
  · intro e _
    have hT : Continuous (fun p : ℝ × AdeleRing (𝓞 F) F =>
        (((σ : ℂ) + (p.1 : ℂ) * Complex.I, (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 p.2 * g) :
          ℂ × AdelicGL2 (𝓞 F) F)) :=
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).prodMk
        ((continuous_const.mul (continuous_unipotentGL2.comp continuous_snd)).mul continuous_const)
    exact ((hψjc e).comp hT).aestronglyMeasurable
  · intro e _
    exact (hm e).1.mul_const _
  · intro e _ t x
    have hbc₀ :=
      exists_mem_adelicBorel_mem_adelicMaximalCompact_weyl_inv_mul_unipotentGL2 F x
    obtain ⟨b, hb, c, hc, hbc⟩ := hbc₀
    have hy : (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g = b * (c * g) := by rw [hbc, mul_assoc]
    have hcg : c * g ∈ Cg := ⟨c, hc, rfl⟩
    have hmt : ‖ψf e ((σ : ℂ) + (t : ℂ) * Complex.I) (c * g)‖ ≤ m e t := (hm e).2 σ le_rfl t (c * g) hcg
    have hm0 : 0 ≤ m e t := (norm_nonneg _).trans hmt
    have hmin' : ‖hσf y₀‖ ≤ ‖hσf (c * g)‖ := hmin hcg
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = (σ : ℂ).re := by simp
    have hprop := norm_mul_mul_norm_eq_of_isInducedSection F α hα (hμ e) (hν e) hre (hψf e _) hsecσ hb (c * g)
    have hone : (1 : ℝ) ≤ ‖hσf y₀‖⁻¹ * ‖hσf (c * g)‖ := by
      have := mul_le_mul_of_nonneg_left hmin' (inv_nonneg.2 hc₀.le)
      rwa [inv_mul_cancel₀ hc₀.ne'] at this
    rw [hy]
    refine le_of_mul_le_mul_right ?_ (hHpos (c * g))
    rw [hprop]
    calc ‖hσf (b * (c * g))‖ * ‖ψf e ((σ : ℂ) + (t : ℂ) * Complex.I) (c * g)‖
        ≤ ‖hσf (b * (c * g))‖ * m e t := mul_le_mul_of_nonneg_left hmt (norm_nonneg _)
      _ = ‖hσf (b * (c * g))‖ * m e t * 1 := (mul_one _).symm
      _ ≤ ‖hσf (b * (c * g))‖ * m e t * (‖hσf y₀‖⁻¹ * ‖hσf (c * g)‖) :=
          mul_le_mul_of_nonneg_left hone (mul_nonneg (norm_nonneg _) hm0)
      _ = m e t * ‖hσf y₀‖⁻¹ * ‖hσf (b * (c * g))‖ * ‖hσf (c * g)‖ := by ring

private theorem exists_forall_norm_weylIntertwiningIntegral_le_mul :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψf s))
      (σ : ℝ) (_hσ : (1 / 2 : ℝ) < σ) (m : ℝ → ℝ)
      (_hm : ∀ (t : ℝ), ∀ g ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)),
        ‖ψf ((σ : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t),
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (t : ℝ), ∀ k ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)),
      ‖weylIntertwiningIntegral (𝓞 F) F (AdelicHaar.adelicAddHaar (𝓞 F) F) (ψf ((σ : ℂ) + (t : ℂ) * Complex.I)) k‖
        ≤ Kc * m t := by
  intro α hα μ ν hμ hν ψf hψf σ hσ m hm

  have hsec₀ := isInducedSection_adelicHeight_cpow F
  obtain ⟨-, h1u, hsec⟩ := hsec₀
  set hσf : AdelicGL2 (𝓞 F) F → ℂ := fun y => ((adelicHeight F y : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) with hσf_def
  have hsecσ : IsInducedSection (𝓞 F) F (etaFst 1 α hα σ) (etaSnd 1 α hα σ) hσf := hsec hα σ
  have hHc : Continuous hσf :=
    (Complex.continuous_ofReal.comp (continuous_adelicHeight F)).cpow continuous_const
      fun y => Complex.ofReal_mem_slitPlane.2 (adelicHeight_pos y)
  have hHnorm : ∀ y, ‖hσf y‖ = adelicHeight F y ^ (σ + 1 / 2) := fun y => by
    rw [hσf_def]
    simp only []
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos y)]
    simp
  have hHpos : ∀ y, 0 < ‖hσf y‖ := fun y => by
    rw [hHnorm]
    exact Real.rpow_pos_of_pos (adelicHeight_pos y) _
  have hMint : Integrable
      (fun x : AdeleRing (𝓞 F) F => ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)‖)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) := by
    have := (weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 h1u h1u (σ : ℂ) (by simpa using hσ) hσf
      hsecσ hHc 1).norm
    simpa only [mul_one] using this

  have hKc : IsCompact (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) := isCompact_adelicMaximalCompact F
  have hKne : (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)).Nonempty := ⟨1, (adelicMaximalCompact F).one_mem⟩
  obtain ⟨y₀, -, hmin⟩ := hKc.exists_isMinOn hKne hHc.norm.continuousOn
  have hc₀ : 0 < ‖hσf y₀‖ := hHpos y₀

  have hKH₀ := exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F _ hKc
  obtain ⟨_, KH, -, hKH⟩ := hKH₀
  set KH' : ℝ := (max KH 0) ^ (σ + 1 / 2) with hKH'_def
  have hKH'0 : 0 ≤ KH' := Real.rpow_nonneg (le_max_right _ _) _
  have hdist : ∀ y : AdelicGL2 (𝓞 F) F, ∀ k ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)),
      ‖hσf (y * k)‖ ≤ KH' * ‖hσf y‖ := by
    intro y k hk
    rw [hHnorm, hHnorm, hKH'_def, ← Real.mul_rpow (le_max_right _ _) (adelicHeight_pos y).le]
    refine Real.rpow_le_rpow (adelicHeight_pos _).le ?_ (by linarith)
    calc adelicHeight F (y * k) ≤ KH * adelicHeight F y := (hKH y k hk).2
      _ ≤ max KH 0 * adelicHeight F y := mul_le_mul_of_nonneg_right (le_max_left _ _) (adelicHeight_pos y).le

  refine ⟨‖hσf y₀‖⁻¹ * KH' * ∫ x, ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)‖ ∂(AdelicHaar.adelicAddHaar (𝓞 F) F),
    mul_nonneg (mul_nonneg (inv_nonneg.2 hc₀.le) hKH'0) (integral_nonneg fun _ => norm_nonneg _), ?_⟩
  intro t k hk
  have hm0 : 0 ≤ m t := (norm_nonneg _).trans (hm t 1 (adelicMaximalCompact F).one_mem)

  have hpt : ∀ x : AdeleRing (𝓞 F) F,
      ‖ψf ((σ : ℂ) + (t : ℂ) * Complex.I) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)‖
        ≤ (m t * (‖hσf y₀‖⁻¹ * KH')) * ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)‖ := by
    intro x
    have hbc₀ :=
      exists_mem_adelicBorel_mem_adelicMaximalCompact_weyl_inv_mul_unipotentGL2 F x
    obtain ⟨b, hb, c, hc, hbc⟩ := hbc₀
    have hck : c * k ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) := (adelicMaximalCompact F).mul_mem hc hk
    have hy : (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k = b * (c * k) := by rw [hbc, mul_assoc]
    have hmt : ‖ψf ((σ : ℂ) + (t : ℂ) * Complex.I) (c * k)‖ ≤ m t := hm t (c * k) hck
    have hmin' : ‖hσf y₀‖ ≤ ‖hσf (c * k)‖ := hmin hck
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = (σ : ℂ).re := by simp
    have hprop := norm_mul_mul_norm_eq_of_isInducedSection F α hα hμ hν hre (hψf _) hsecσ hb (c * k)
    have hstep : ‖ψf ((σ : ℂ) + (t : ℂ) * Complex.I) (b * (c * k))‖ ≤ ‖hσf (b * (c * k))‖ * m t / ‖hσf y₀‖ := by
      refine le_trans ?_ (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) hm0) hc₀ hmin')
      rw [le_div_iff₀ (hHpos (c * k)), hprop]
      exact mul_le_mul_of_nonneg_left hmt (norm_nonneg _)
    have hheight : ‖hσf (b * (c * k))‖ ≤ KH' * ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)‖ := by
      rw [← hy]
      exact hdist _ k hk
    rw [hy]
    calc ‖ψf ((σ : ℂ) + (t : ℂ) * Complex.I) (b * (c * k))‖
        ≤ ‖hσf (b * (c * k))‖ * m t / ‖hσf y₀‖ := hstep
      _ ≤ KH' * ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)‖ * m t / ‖hσf y₀‖ := by
          gcongr
      _ = (m t * (‖hσf y₀‖⁻¹ * KH')) * ‖hσf ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)‖ := by ring
  unfold weylIntertwiningIntegral
  refine (norm_integral_le_of_norm_le (hMint.const_mul _) (Filter.Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul]
  ring

end KeyClose
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end WeylLineInterchange
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hcT : c ≠ ∞)
      (_hc : ∀ H : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable H →
        ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                H (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ι)
        (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (r : ι → ι) (_hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
      (_hdist : ∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)
      (φf ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hφdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (_hψ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (σ : ℝ) (_hσ : (1 / 2 : ℝ) < σ),
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (AutomorphicForm.pseudoEisenstein F ψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / (16 * Real.pi) : ℝ) : ℂ) *
    ∑ e, ∫ t : ℝ,
      ((∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (ψf e (-(σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F))
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
                (ψf (r e) ((σ : ℂ) - (t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F)) := by
  intro α hα d₁ d₂ hd₁ hd Φ hΦs hΦ c hc0 hcT hc D _ hDF V _ hVT hV ξ ι _ μ ν hμ hν hμic hνic hμc hμν r hr hdist
    φf ψf hφf hψf hφjc hψjc hφhol hφdec hψdec φ ψ hφ hψ hφrep hψrep σ hσ
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SigmaFinite (NumberField.Idele.idelicHaar F) := IwasawaQuotientDisintegration.sigmaFinite_idelicHaar F
  haveI : Measure.IsAddHaarMeasure (adelicAddHaar (𝓞 F) F) := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : SFinite (adelicAddHaar (𝓞 F) F) := inferInstance
  have hZ : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      x ∈ (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z :=
      fun x => by
    rw [productionPinsOf_Z]
    exact Subgroup.mem_top x
  refine (AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_pseudoEisenstein_eq_setIntegral_quotient_slab F d₁ d₂
    hd₁ hd Φ hΦs hΦ ξ φ ψ hφ hψ).trans ?_
  refine (ParsevalAboveFloor.setIntegral_quotient_slab_eq (F := F) d₁ d₂ hd₁ hd
    (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂)
    ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal (cQ := c * adelicAddHaar (𝓞 F) F (adelicBox F))
    (ENNReal.mul_ne_top hcT (adelicAddHaar_adelicBox_lt_top F).ne) (D := D)
    (fun f hf hfH =>
      IwasawaQuotientDisintegration.lintegral_out_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
        hc0 hc hDF hDF f hf hfH)
    (IwasawaQuotientDisintegration.measurable_centralScalar_mul_diagOne_mul F)
    (NumberField.TateGlobal.continuous_ideleNorm F).measurable hDF hV hVT (isCompact_adelicMaximalCompact F) μ ν hμ hν
    hμic hνic hμc (ξ := fun x => ξ ⟨x, hZ x⟩) (fun e x => hμν e ⟨x, hZ x⟩) r hr hdist hα
    (fun u => Units.val_eq_one.mp ((ParsevalAboveFloor.normChar_apply F _).trans
      (IdeleClassPairing.ideleNorm_eq_one_of_mem_principalIdeles (MonoidHom.mem_range.mpr ⟨u, rfl⟩))))
    φf ψf hφf hψf hφjc hψjc hφhol hφdec hψdec φ ψ hφ.measurable hψ.measurable
    (EisensteinTorusFacts.apply_mul_of_mem_of_isSlabProfile hφ)
    (EisensteinTorusFacts.apply_mul_of_mem_of_isSlabProfile hψ)
    (fun z g => hφ.central_transform ⟨z, hZ z⟩ g) (fun z g => hψ.central_transform ⟨z, hZ z⟩ g) hφrep hψrep σ hσ
    (WeylLineInterchange.weylIntertwiningIntegral_eq_sum_integral_weylIntertwiningIntegral F hα ι μ ν hμ hν ψf hψf hψjc
      (fun e σ₀ C hC => (hψdec e σ₀ C hC).imp fun m hm => ⟨hm.1, hm.2.2⟩) ψ hψrep σ hσ)
    (fun e s => AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hα (μ e) (ν e) s (ψf e s)
      (hψf e s))
    (fun e m hm => WeylLineInterchange.exists_forall_norm_weylIntertwiningIntegral_le_mul F hα (hμ e) (hν e) (ψf e)
      (hψf e) σ hσ m hm)).trans ?_
  congr 1
  rw [ENNReal.toReal_mul]
  push_cast
  ring

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IdeleClassPairing P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.IwasawaQuotientDisintegration"

end S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab (solution)
