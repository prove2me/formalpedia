-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/86bce99e-e4d2-5fc6-88ba-0f85235f1a6e

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window
import Theorems.Thm_AutomorphicForm_lintegral_canonicalTruncationDomain_enorm_pseudoEisenstein_mul_enorm_truncatedSection_add_tsum_lt_top_of_re_lt_re
import Theorems.Thm_AutomorphicForm_exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
import Theorems.Thm_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace MaassSelbergOneHeight

open AutomorphicForm NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (F : Type) [Field F] [NumberField F]

theorem eta_product_conj_eq₂ (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν) (s₁ s₂ : ℂ) (z t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst μ α hα s₁ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₁ z : ℂˣ) : ℂ) *
        conj (((etaFst μ α hα s₂ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₂ z : ℂˣ) : ℂ)) =
      ((ideleNorm F t : ℝ) : ℂ) ^ (s₁ + conj s₂ + 1) := by
  have hnorm : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = ideleNorm F x := by
    intro x; rw [hαdef]; rfl
  have hpos : ∀ x : (AdeleRing (𝓞 F) F)ˣ, 0 < ideleNorm F x := fun x => (hnorm x) ▸ hα x
  have hunit : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((μ x : ℂˣ) : ℂ) * conj ((μ x : ℂˣ) : ℂ) = 1 := by
    intro x
    rw [Complex.mul_conj, ← Complex.sq_norm, hμ x]
    norm_num
  have hunitν : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((ν x : ℂˣ) : ℂ) * conj ((ν x : ℂˣ) : ℂ) = 1 := by
    intro x
    rw [Complex.mul_conj, ← Complex.sq_norm, hν x]
    norm_num
  have hconj : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, conj (((r : ℝ) : ℂ) ^ w) = ((r : ℝ) : ℂ) ^ (conj w) := by
    intro r hr w
    have harg : ((r : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val, hnorm, map_mul]
  rw [hconj _ (hpos z), hconj _ (hpos t), hconj _ (hpos z)]
  simp only [map_add, map_neg, map_div₀, map_one, map_ofNat]
  set Z : ℂ := ((ideleNorm F z : ℝ) : ℂ) with hZ
  set T : ℂ := ((ideleNorm F t : ℝ) : ℂ) with hT
  have hZ0 : Z ≠ 0 := by rw [hZ]; exact_mod_cast (hpos z).ne'
  have hT0 : T ≠ 0 := by rw [hT]; exact_mod_cast (hpos t).ne'
  have hcanc : ∀ w : ℂ, Z ^ w * Z ^ (-w) = 1 := by
    intro w
    rw [Complex.cpow_neg, mul_inv_cancel₀]
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hZ0
  calc _ = (((μ z : ℂˣ) : ℂ) * conj ((μ z : ℂˣ) : ℂ)) * (((ν z : ℂˣ) : ℂ) * conj ((ν z : ℂˣ) : ℂ)) *
          (((μ t : ℂˣ) : ℂ) * conj ((μ t : ℂˣ) : ℂ)) *
          (Z ^ (s₁ + 1 / 2) * Z ^ (-(s₁ + 1 / 2))) * (Z ^ (conj s₂ + 1 / 2) * Z ^ (-(conj s₂ + 1 / 2))) *
          (T ^ (s₁ + 1 / 2) * T ^ (conj s₂ + 1 / 2)) := by ring
    _ = T ^ (s₁ + conj s₂ + 1) := by
        rw [hunit z, hunitν z, hunit t, hcanc, hcanc, ← Complex.cpow_add _ _ hT0]
        simp only [one_mul]
        congr 1
        ring

theorem measurable_ideleNorm : Measurable (ideleNorm F) := (continuous_ideleNorm F).measurable

theorem exists_norm_pushforward (D : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F)) :
    ∃ V : ℝ≥0∞, V ≠ 0 ∧ V ≠ ∞ ∧
      (∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹) ∧
      Measure.map (ideleNorm F) ((NumberField.Idele.idelicHaar F).restrict D) =
        V • (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y => ENNReal.ofReal y⁻¹) := by
  obtain ⟨V, hV0, hVT, hV⟩ := NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi F D hD hDF
  refine ⟨V, hV0, hVT, hV, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_ideleNorm F) hs, Measure.smul_apply, withDensity_apply _ hs,
    Measure.restrict_restrict hs, smul_eq_mul]
  have h1 : ((NumberField.Idele.idelicHaar F).restrict D) (ideleNorm F ⁻¹' s) =
      ∫⁻ z in D, s.indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) := by
    rw [← lintegral_indicator_one ((measurable_ideleNorm F) hs)]
    rfl
  rw [h1, hV _ (measurable_const.indicator hs)]
  congr 1
  rw [← Measure.restrict_restrict hs, ← lintegral_indicator hs]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ s <;> simp [hy]

theorem ofReal_exp_cpow (R : ℝ) (X : ℂ) : ((Real.exp R : ℝ) : ℂ) ^ X = Complex.exp ((R : ℂ) * X) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos R).ne'), Complex.ofReal_exp,
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_pos.le), mul_comm]

theorem setIntegral_Ioc_zero_exp_cpow_sub_one {X : ℂ} (hX : 0 < X.re) (R : ℝ) :
    ∫ y in Set.Ioc 0 (Real.exp R), ((y : ℝ) : ℂ) ^ (X - 1) = Complex.exp ((R : ℂ) * X) / X := by
  have hX0 : X ≠ 0 := fun h => by rw [h, Complex.zero_re] at hX; exact lt_irrefl _ hX
  rw [← intervalIntegral.integral_of_le (Real.exp_pos R).le, integral_cpow, sub_add_cancel, ofReal_exp_cpow,
    Complex.ofReal_zero, Complex.zero_cpow hX0, sub_zero]
  left
  simpa using hX

theorem setIntegral_Ioi_exp_cpow_sub_one {X : ℂ} (hX : X.re < 0) (R : ℝ) :
    ∫ y in Set.Ioi (Real.exp R), ((y : ℝ) : ℂ) ^ (X - 1) = -(Complex.exp ((R : ℂ) * X) / X) := by
  rw [integral_Ioi_cpow_of_lt (by rw [Complex.sub_re, Complex.one_re]; linarith) (Real.exp_pos R), sub_add_cancel,
    ofReal_exp_cpow, neg_div]

theorem lintegral_Iic_inter_Ioi_rpow_lt_top {p : ℝ} (hp : -1 < p) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in Set.Iic T ∩ Set.Ioi 0, ENNReal.ofReal (y ^ p) < ∞ := by
  have hI : IntegrableOn (fun y : ℝ => y ^ p) (Set.Ioc 0 T) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hp (a := 0) (b := T)).1
  rw [Set.inter_comm, Set.Ioi_inter_Iic]
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hI.2

theorem lintegral_Ioi_inter_Ioi_rpow_lt_top {p : ℝ} (hp : p < -1) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in Set.Ioi T ∩ Set.Ioi 0, ENNReal.ofReal (y ^ p) < ∞ := by
  have hI : IntegrableOn (fun y : ℝ => y ^ p) (Set.Ioi T) volume := integrableOn_Ioi_rpow_of_lt hp hT
  rw [Set.inter_eq_self_of_subset_left (Set.Ioi_subset_Ioi hT.le)]
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hI.2

theorem setIntegral_comp_ideleNorm_eq (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (V : ℝ≥0∞) (hV : Measure.map (ideleNorm F) ((NumberField.Idele.idelicHaar F).restrict D) =
        V • (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y => ENNReal.ofReal y⁻¹))
    (g : ℝ → ℂ) (hg : Measurable g) :
    ∫ z in D, g (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
      (V.toReal : ℂ) * ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * g y := by
  have h1 : ∫ z in D, g (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
      ∫ y, g y ∂(Measure.map (ideleNorm F) ((NumberField.Idele.idelicHaar F).restrict D)) := by
    rw [integral_map (measurable_ideleNorm F).aemeasurable hg.aestronglyMeasurable]
  rw [h1, hV, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (measurable_inv.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [Complex.real_smul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (le_of_lt hy)), Complex.real_smul]

theorem isInducedSection_const_mul {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (c : ℂ) (h : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) :
    IsInducedSection (𝓞 F) F χ₁ χ₂ (fun g => c * φ g) := by
  intro b hb g
  show c * φ (b * g) = _
  rw [h b hb g]
  ring

end MaassSelbergOneHeight

namespace MaassSelbergOneHeight

open AutomorphicForm NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (F : Type) [Field F] [NumberField F]

theorem sigmaFinite_restrict_idelicHaar (D : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hpos : ∀ t : (AdeleRing (𝓞 F) F)ˣ, 0 < ideleNorm F t) :
    SigmaFinite ((NumberField.Idele.idelicHaar F).restrict D) := by
  refine Measure.sigmaFinite_of_countable
    (S := Set.range fun n : ℕ =>
      {t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ∈ Set.Icc (Real.exp (-((n : ℝ) + 1))) (Real.exp ((n : ℝ) + 1))})
    (Set.countable_range _) ?_ ?_
  · rintro s ⟨n, rfl⟩
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp only
    rw [Measure.restrict_apply' hD, Set.inter_comm]
    exact (NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D hD hDF _ _ (Real.exp_pos _)
      (Real.exp_lt_exp.mpr (by linarith))).2
  · refine Set.eq_univ_of_forall fun t => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |Real.log (ideleNorm F t)|
    refine Set.mem_sUnion.mpr ⟨_, ⟨n, rfl⟩, ?_⟩
    show ideleNorm F t ∈ Set.Icc _ _
    rw [← Real.exp_log (hpos t)]
    constructor
    · exact Real.exp_le_exp.mpr (by have := neg_abs_le (Real.log (ideleNorm F t)); linarith)
    · exact Real.exp_le_exp.mpr (by have := le_abs_self (Real.log (ideleNorm F t)); linarith)

theorem torus_window_integral_eq (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν)
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (a b : ℝ)
    (Cz : ℝ≥0∞) (hCzT : Cz ≠ ∞)
    (hCz : ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar F) (D ∩ {z | ideleNorm F z ^ 2 * r ∈ Set.Icc a b}) = Cz)
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hVl : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D', f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hV : Measure.map (ideleNorm F) ((NumberField.Idele.idelicHaar F).restrict D') =
        V • (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y => ENNReal.ofReal y⁻¹))
    (s₁ s₂ : ℂ) (I : Set ℝ) (hI : MeasurableSet I)
    (hIint : ∫⁻ y in I ∩ Set.Ioi 0, ENNReal.ofReal (y ^ ((s₁ + conj s₂).re - 1)) < ∞) :
    ∫ z in D, ∫ t in D',
        ((etaFst μ α hα s₁ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₁ z : ℂˣ) : ℂ) *
          conj (((etaFst μ α hα s₂ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₂ z : ℂˣ) : ℂ)) *
          (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
          I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
          (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) =
    (Cz.toReal : ℂ) * (V.toReal : ℂ) * ∫ y in I ∩ Set.Ioi 0, ((y : ℝ) : ℂ) ^ (s₁ + conj s₂ - 1) := by
  set X : ℂ := s₁ + conj s₂ with hXdef
  set H := NumberField.Idele.idelicHaar F with hH
  have hnorm : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = ideleNorm F x := by intro x; rw [hαdef]; rfl
  have hpos : ∀ x : (AdeleRing (𝓞 F) F)ˣ, 0 < ideleNorm F x := fun x => (hnorm x) ▸ hα x
  haveI : SigmaFinite (H.restrict D) := sigmaFinite_restrict_idelicHaar F D hD hDF hpos
  haveI : SigmaFinite (H.restrict D') := sigmaFinite_restrict_idelicHaar F D' hD' hD'F hpos
  set S : (AdeleRing (𝓞 F) F)ˣ → Set (AdeleRing (𝓞 F) F)ˣ := fun t =>
    {z | ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b} with hSdef
  have hSm : ∀ t, MeasurableSet (S t) := fun t =>
    measurableSet_Icc.preimage (((measurable_ideleNorm F).pow_const 2).mul_const _)

  set wfn : ℝ → ℂ := fun y => I.indicator (fun _ => (1 : ℂ)) y * ((y : ℝ) : ℂ) ^ X with hwfn
  have hwm : Measurable wfn :=
    (measurable_const.indicator hI).mul (Complex.measurable_ofReal.pow_const X)
  set f : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ → ℂ := fun z t =>
    (S t).indicator (fun _ => (1 : ℂ)) z * wfn (ideleNorm F t) with hfdef
  have hpt : ∀ z t, ((etaFst μ α hα s₁ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₁ z : ℂˣ) : ℂ) *
          conj (((etaFst μ α hα s₂ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₂ z : ℂˣ) : ℂ)) *
          (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
          I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
          (((ideleNorm F t)⁻¹ : ℝ) : ℂ) = f z t := by
    intro z t
    rw [eta_product_conj_eq₂ F α hαdef hα μ ν hμ hν s₁ s₂ z t]
    have hT0 : ((ideleNorm F t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos t).ne'
    have hind : (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) =
        (S t).indicator (fun _ => (1 : ℂ)) z := by
      by_cases h : ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show z ∈ S t from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show z ∉ S t from h)]
    rw [hind]
    show _ = (S t).indicator (fun _ => (1 : ℂ)) z *
      (I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) * ((ideleNorm F t : ℝ) : ℂ) ^ X)
    rw [← hXdef, Complex.cpow_add _ _ hT0, Complex.cpow_one, Complex.ofReal_inv]
    field_simp
  simp_rw [hpt]

  have hmeasf : Measurable (Function.uncurry f) := by
    have h1 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ =>
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2) :=
      (measurable_const.indicator measurableSet_Icc).comp
        ((((measurable_ideleNorm F).comp measurable_fst).pow_const 2).mul
          ((measurable_ideleNorm F).comp measurable_snd))
    have h2 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ => wfn (ideleNorm F p.2) :=
      hwm.comp ((measurable_ideleNorm F).comp measurable_snd)
    have h1' : (fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ =>
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2)) =
        fun p => (S p.2).indicator (fun _ => (1 : ℂ)) p.1 := by
      funext p
      by_cases h : ideleNorm F p.1 ^ 2 * ideleNorm F p.2 ∈ Set.Icc a b
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p.1 ∈ S p.2 from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show p.1 ∉ S p.2 from h)]
    rw [h1'] at h1
    exact h1.mul h2

  set g : ℝ → ℝ≥0∞ := fun y => I.indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal (y ^ X.re) with hgdef
  have hgm : Measurable g :=
    (measurable_const.indicator hI).mul (measurable_id.pow_const X.re).ennreal_ofReal
  have hnf : ∀ z t, ‖f z t‖ₑ = (S t).indicator (fun _ => (1 : ℝ≥0∞)) z * g (ideleNorm F t) := by
    intro z t
    show ‖(S t).indicator (fun _ => (1 : ℂ)) z * (I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
      ((ideleNorm F t : ℝ) : ℂ) ^ X)‖ₑ =
      (S t).indicator (fun _ => (1 : ℝ≥0∞)) z *
        (I.indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F t) * ENNReal.ofReal (ideleNorm F t ^ X.re))
    rw [enorm_mul, enorm_mul, ← ofReal_norm (((ideleNorm F t : ℝ) : ℂ) ^ X),
      Complex.norm_cpow_eq_rpow_re_of_pos (hpos t)]
    congr 1
    · by_cases h : z ∈ S t
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
    · congr 1
      by_cases h : ideleNorm F t ∈ I
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

  have hinner : ∀ t, ∫⁻ z, ‖Function.uncurry f (z, t)‖ₑ ∂(H.restrict D) = Cz * g (ideleNorm F t) := by
    intro t
    show ∫⁻ z in D, ‖f z t‖ₑ ∂H = _
    simp_rw [hnf]
    rw [lintegral_mul_const _ (measurable_const.indicator (hSm t)), lintegral_indicator_const (hSm t),
      Measure.restrict_apply (hSm t), Set.inter_comm, hCz _ (hpos t), one_mul]
  have hlin : ∫⁻ p, ‖Function.uncurry f p‖ₑ ∂((H.restrict D).prod (H.restrict D')) < ∞ := by
    rw [lintegral_prod_symm _ hmeasf.enorm.aemeasurable]
    simp_rw [hinner]
    rw [lintegral_const_mul'' Cz (f := fun t => g (ideleNorm F t))
      ((hgm.comp (measurable_ideleNorm F)).aemeasurable)]
    refine ENNReal.mul_lt_top hCzT.lt_top ?_
    rw [show (∫⁻ t in D', g (ideleNorm F t) ∂H) = V * ∫⁻ y in Set.Ioi (0 : ℝ), g y * ENNReal.ofReal y⁻¹
      from hVl g hgm]
    refine ENNReal.mul_lt_top hVT.lt_top ?_
    have hpt' : ∀ y ∈ Set.Ioi (0 : ℝ), g y * ENNReal.ofReal y⁻¹ =
        I.indicator (fun y => ENNReal.ofReal (y ^ (X.re - 1))) y := by
      intro y hy
      by_cases h : y ∈ I
      · simp only [hgdef, Set.indicator_of_mem h, one_mul]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hy) _), Real.rpow_sub_one (ne_of_gt hy),
          div_eq_mul_inv]
      · simp only [hgdef, Set.indicator_of_notMem h, zero_mul]
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt', lintegral_indicator hI, Measure.restrict_restrict hI]
    exact hIint
  have hint : Integrable (Function.uncurry f) ((H.restrict D).prod (H.restrict D')) :=
    ⟨hmeasf.aestronglyMeasurable, hlin⟩
  rw [integral_integral_swap hint]

  have hzint : ∀ t, ∫ z in D, f z t ∂H = (Cz.toReal : ℂ) * wfn (ideleNorm F t) := by
    intro t
    show ∫ z in D, (S t).indicator (fun _ => (1 : ℂ)) z * wfn (ideleNorm F t) ∂H = _
    rw [integral_mul_const, integral_indicator_const (1 : ℂ) (hSm t), Measure.real, Measure.restrict_apply (hSm t),
      Set.inter_comm, hCz _ (hpos t)]
    simp
  have hzint' : (fun t => ∫ z in D, f z t ∂H) = fun t => (Cz.toReal : ℂ) * wfn (ideleNorm F t) := funext hzint
  show ∫ t in D', (fun t => ∫ z in D, f z t ∂H) t ∂H = _
  rw [hzint', integral_const_mul, setIntegral_comp_ideleNorm_eq F D' V hV wfn hwm]

  have hhalf : ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * wfn y = ∫ y in I ∩ Set.Ioi 0, ((y : ℝ) : ℂ) ^ (X - 1) := by
    have hpt'' : ∀ y ∈ Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * wfn y =
        I.indicator (fun y => ((y : ℝ) : ℂ) ^ (X - 1)) y := by
      intro y hy
      by_cases h : y ∈ I
      · simp only [hwfn, Set.indicator_of_mem h, one_mul]
        rw [Complex.cpow_sub _ _ (by exact_mod_cast (ne_of_gt hy : y ≠ 0)), Complex.cpow_one, Complex.ofReal_inv]
        field_simp
      · simp only [hwfn, Set.indicator_of_notMem h, zero_mul, mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt'', setIntegral_indicator hI, Set.inter_comm]
  rw [hhalf]
  ring

theorem torus_halfline_lo (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν)
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (a b : ℝ)
    (Cz : ℝ≥0∞) (hCzT : Cz ≠ ∞)
    (hCz : ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar F) (D ∩ {z | ideleNorm F z ^ 2 * r ∈ Set.Icc a b}) = Cz)
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hVl : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D', f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hV : Measure.map (ideleNorm F) ((NumberField.Idele.idelicHaar F).restrict D') =
        V • (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y => ENNReal.ofReal y⁻¹))
    (s₁ s₂ : ℂ) (hX : 0 < (s₁ + conj s₂).re) (R : ℝ) :
    ∫ z in D, ∫ t in D',
        ((etaFst μ α hα s₁ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₁ z : ℂˣ) : ℂ) *
          conj (((etaFst μ α hα s₂ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₂ z : ℂˣ) : ℂ)) *
          (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
          (Set.Iic (Real.exp R)).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
          (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) =
    (Cz.toReal : ℂ) * (V.toReal : ℂ) * (Complex.exp ((R : ℂ) * (s₁ + conj s₂)) / (s₁ + conj s₂)) := by
  rw [torus_window_integral_eq F α hαdef hα μ ν hμ hν D D' hD hD' hDF hD'F a b Cz hCzT hCz V hVT hVl hV s₁ s₂
    (Set.Iic (Real.exp R)) measurableSet_Iic
    (lintegral_Iic_inter_Ioi_rpow_lt_top (by linarith) _ (Real.exp_pos R)),
    Set.inter_comm, Set.Ioi_inter_Iic, setIntegral_Ioc_zero_exp_cpow_sub_one hX]

theorem torus_halfline_hi (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν)
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (a b : ℝ)
    (Cz : ℝ≥0∞) (hCzT : Cz ≠ ∞)
    (hCz : ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar F) (D ∩ {z | ideleNorm F z ^ 2 * r ∈ Set.Icc a b}) = Cz)
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hVl : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D', f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hV : Measure.map (ideleNorm F) ((NumberField.Idele.idelicHaar F).restrict D') =
        V • (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y => ENNReal.ofReal y⁻¹))
    (s₁ s₂ : ℂ) (hX : (s₁ + conj s₂).re < 0) (R : ℝ) :
    ∫ z in D, ∫ t in D',
        ((etaFst μ α hα s₁ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₁ z : ℂˣ) : ℂ) *
          conj (((etaFst μ α hα s₂ (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s₂ z : ℂˣ) : ℂ)) *
          (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
          (Set.Ioi (Real.exp R)).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
          (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) =
    (Cz.toReal : ℂ) * (V.toReal : ℂ) * (-(Complex.exp ((R : ℂ) * (s₁ + conj s₂)) / (s₁ + conj s₂))) := by
  rw [torus_window_integral_eq F α hαdef hα μ ν hμ hν D D' hD hD' hDF hD'F a b Cz hCzT hCz V hVT hVl hV s₁ s₂
    (Set.Ioi (Real.exp R)) measurableSet_Ioi
    (lintegral_Ioi_inter_Ioi_rpow_lt_top (by linarith) _ (Real.exp_pos R)),
    Set.inter_eq_self_of_subset_left (Set.Ioi_subset_Ioi (Real.exp_pos R).le), setIntegral_Ioi_exp_cpow_sub_one hX]

end MaassSelbergOneHeight

namespace MaassSelbergOneHeight

open AutomorphicForm NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] {μ : Measure X} {s S : Set X}
    (hS : MeasurableSet S) (hsub : s ⊆ S) (h : NullMeasurableSet s (μ.restrict S)) : NullMeasurableSet s μ := by
  obtain ⟨t, ht, hst⟩ := h
  refine ⟨t ∩ S, ht.inter hS, ?_⟩
  rw [ae_eq_set] at hst ⊢
  obtain ⟨h1, h2⟩ := hst
  rw [Measure.restrict_apply' hS] at h1 h2
  have e1 : s \ (t ∩ S) = (s \ t) ∩ S := by
    ext x
    simp only [Set.mem_diff, Set.mem_inter_iff, not_and_or]
    constructor
    · rintro ⟨hs, ht'⟩
      rcases ht' with ht' | ht'
      · exact ⟨⟨hs, ht'⟩, hsub hs⟩
      · exact absurd (hsub hs) ht'
    · rintro ⟨⟨hs, ht'⟩, -⟩
      exact ⟨hs, Or.inl ht'⟩
  have e2 : (t ∩ S) \ s = (t \ s) ∩ S := by
    ext x
    simp only [Set.mem_diff, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨ht', hS'⟩, hs⟩; exact ⟨⟨ht', hs⟩, hS'⟩
    · rintro ⟨⟨ht', hs⟩, hS'⟩; exact ⟨⟨ht', hS'⟩, hs⟩
  rw [e1, e2]
  exact ⟨h1, h2⟩

theorem oneHeight
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hμν : μ = ν)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re) (_hne : s ≠ conj s') (_hlt : s.re < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s') (AutomorphicForm.etaSnd ν αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (c : ℂ) *
        ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ) := by
  intro αm hαm
  classical
  have hαdef : αm = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
      (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits := rfl
  have hnorm : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((αm x : ℝˣ) : ℝ) = ideleNorm F x := by intro x; rfl
  have hpos : ∀ x : (AdeleRing (𝓞 F) F)ˣ, 0 < ideleNorm F x := fun x => (hnorm x) ▸ hαm x

  obtain ⟨hfl, hTc, hΦS, hΦs, hFD⟩ := canonicalTruncationData_isTruncationDatum F α β hα hαβ

  obtain ⟨cIw, hcIw0, hcIwT, hcIw⟩ := exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  obtain ⟨D, hDm, hDF, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F
      (NumberField.Idele.idelicHaar F)
  obtain ⟨Cz, hCz0, hCzT, hCz⟩ :=
    NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F D hDm hDF α β hα hαβ
  obtain ⟨V, hV0, hVT, hVl, hV⟩ := exists_norm_pushforward F D hDm hDF
  obtain ⟨T₀, hT₀, hadj⟩ :=
    exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
      F α β hα hαβ
  obtain ⟨R₂, hR₂⟩ :=
    exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
      F α β hα hαβ ΦF hαm
  have hcIwpos : 0 < cIw.toReal := ENNReal.toReal_pos hcIw0 hcIwT
  have hCzpos : 0 < Cz.toReal := ENNReal.toReal_pos hCz0 hCzT
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos hV0 hVT
  refine ⟨cIw.toReal * (Cz.toReal * V.toReal), mul_pos hcIwpos (mul_pos hCzpos hVpos), max (Real.log T₀) R₂, ?_⟩
  intro μ ν hμν hμ hν hμF hνF s s' hs hs' hne hlt φ hφ hφc hφK hφf ψ hψ hψc hψK hψf R hR
  subst hμν
  have hRT : T₀ ≤ Real.exp R := by
    have h1 : Real.log T₀ ≤ R := le_trans (le_max_left _ _) hR
    calc T₀ = Real.exp (Real.log T₀) := (Real.exp_log hT₀).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr h1
  have hR₂R : R₂ ≤ R := le_trans (le_max_right _ _) hR

  set vol : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℝ) : ℂ) with hvol
  set Mφ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    vol⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g with hMφdef
  set Mψ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    vol⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g with hMψdef
  have hMφ : IsInducedSection (𝓞 F) F (etaFst μ αm hαm (-s)) (etaSnd μ αm hαm (-s)) Mφ :=
    isInducedSection_const_mul F _ (isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hαm μ μ s φ hφ)
  have hMψ : IsInducedSection (𝓞 F) F (etaFst μ αm hαm (-s')) (etaSnd μ αm hαm (-s')) Mψ :=
    isInducedSection_const_mul F _ (isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hαm μ μ s' ψ hψ)
  have hMφc : Continuous Mφ :=
    continuous_const.mul (continuous_weylIntertwiningIntegral_of_re_gt_half F hαm μ μ hμ hμ s hs φ hφ hφc)
  have hMψc : Continuous Mψ :=
    continuous_const.mul (continuous_weylIntertwiningIntegral_of_re_gt_half F hαm μ μ hμ hμ s' hs' ψ hψ hψc)

  set E : AdelicGL2 (𝓞 F) F → ℂ := pseudoEisenstein F φ with hE
  set E' : AdelicGL2 (𝓞 F) F → ℂ := pseudoEisenstein F ψ with hE'
  have hEc : Continuous E :=
    hφc.add (continuous_bruhatTransversal_tsum_of_re_gt_half F hαm μ μ hμ hμ s hs φ hφ hφc)
  have hE'c : Continuous E' :=
    hψc.add (continuous_bruhatTransversal_tsum_of_re_gt_half F hαm μ μ hμ hμ s' hs' ψ hψ hψc)
  have hEinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      E (globalPoints (𝓞 F) F γ * g) = E g := fun γ g =>
    (pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F φ
      (IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul F hαm μ μ hμF hμF
        s φ hφ).1 g
      ((bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ μ hμ hμ s hs φ hφ hφc g).of_norm) γ).2
  have hE'inv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      E' (globalPoints (𝓞 F) F γ * g) = E' g := fun γ g =>
    (pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F ψ
      (IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul F hαm μ μ hμF hμF
        s' ψ hψ).1 g
      ((bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ μ hμ hμ s' hs' ψ hψ hψc g).of_norm) γ).2
  have hEB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, E (globalPoints (𝓞 F) F γ * g) = E g :=
    fun γ _ g => hEinv γ g
  have hE'B : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, E' (globalPoints (𝓞 F) F γ * g) = E' g :=
    fun γ _ g => hE'inv γ g

  set ψR : AdelicGL2 (𝓞 F) F → ℂ := fun x =>
    if NumberField.AdelicHeight.adelicHeight F x ≤ Real.exp R then ψ x else -(Mψ x) with hψRdef
  set p : AdelicGL2 (𝓞 F) F → ℂ := fun x => conj (ψR x) with hpdef
  obtain ⟨hψB, hψN⟩ :=
    IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul F hαm μ μ hμF hμF s' ψ hψ
  obtain ⟨hMψB, hMψN⟩ :=
    IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul F hαm μ μ hμF hμF (-s')
      Mψ hMψ
  obtain ⟨hHN, -⟩ := NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul F
  have hHB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F (globalPoints (𝓞 F) F γ * g) =
        NumberField.AdelicHeight.adelicHeight F g :=
    fun γ hγ g => NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ hγ g
  have hpB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F, p (globalPoints (𝓞 F) F γ * x) = p x := by
    intro γ hγ x
    simp only [hpdef, hψRdef, hHB γ hγ x, hψB γ hγ x, hMψB γ hγ x]
  have hpN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), p (unipotentGL2 u * x) = p x := by
    intro u x
    simp only [hpdef, hψRdef, hHN u x, hψN u x, hMψN u x]
  have hmH : Measurable (NumberField.AdelicHeight.adelicHeight F) :=
    (NumberField.AdelicHeight.continuous_adelicHeight F).measurable
  have hψRm : Measurable ψR :=
    Measurable.ite (measurableSet_le hmH measurable_const) hψc.measurable hMψc.measurable.neg
  have hpm : Measurable p := Complex.continuous_conj.measurable.comp hψRm

  have hSm : MeasurableSet {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
    NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F α β
  have hdetG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F),
      ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * x)) =
        ideleNorm F (Matrix.GeneralLinearGroup.det x) := by
    intro γ x
    rw [map_mul, ← hnorm, map_mul, Units.val_mul, hnorm, hnorm, ideleNorm_det_globalPoints, one_mul]
  have hdetN : ∀ (u : AdeleRing (𝓞 F) F),
      Matrix.GeneralLinearGroup.det (unipotentGL2 u : AdelicGL2 (𝓞 F) F) = 1 := by
    intro u
    ext
    simp [Matrix.det_fin_two_of]
  have hSG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F),
      globalPoints (𝓞 F) F γ * x ∈ {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ↔ x ∈ {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
    intro γ x
    simp only [Set.mem_setOf_eq, hdetG]
  have hSN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F),
      unipotentGL2 u * x ∈ {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ↔ x ∈ {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
    intro u x
    simp only [Set.mem_setOf_eq, map_mul, hdetN, one_mul]
  have hΦnull : NullMeasurableSet (canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    nullMeasurableSet_of_restrict hSm hΦs hFD.nullMeasurableSet

  have hABS :=
    lintegral_canonicalTruncationDomain_enorm_pseudoEisenstein_mul_enorm_truncatedSection_add_tsum_lt_top_of_re_lt_re
      F α β hα hαβ hαm μ μ μ μ hμ hμ hμ hμ hμF hμF hμF hμF s s' hs hs' hlt φ hφ hφc hφK hφf ψ hψ hψc hψK hψf R
  have hfin : ∫⁻ x in canonicalTruncationDomain F α β, ‖E x‖ₑ * (‖p x‖ₑ + ∑' ξ : F,
        ‖p (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞ := by
    simp only [hpdef, RCLike.enorm_conj]
    exact hABS

  obtain ⟨hIEθ, -, -, hUnf⟩ :=
    setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul F
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} hSm hSG hSN
      (canonicalTruncationDomain F α β) hΦs hFD E p hEc.measurable hpm hEinv hpB hpN hfin

  have h2nd : ∀ g ∈ canonicalTruncationDomain F α β,
      lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' g = pseudoEisenstein F ψR g :=
    fun g hg => hR₂ R hR₂R μ μ hμ hμ s' hs' ψ hψ hψc g hg
  have hconjθ : ∀ g, conj (pseudoEisenstein F ψR g) = pseudoEisenstein F p g := by
    intro g
    simp only [pseudoEisenstein_apply, map_add, Complex.conj_tsum, hpdef]

  have hL2φ : MemLp (fun x => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E x) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) :=
    memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain F α β hα hαβ ΦF hαm μ μ hμ hμ s hs φ hφ
      hφc hφK hφf R
  have hL2ψ : MemLp (fun x => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) :=
    memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain F α β hα hαβ ΦF hαm μ μ hμ hμ s' hs' ψ hψ
      hψc hψK hψf R
  refine ⟨hL2φ.integrable_mul hL2ψ.star, ?_⟩

  have hIΛΛ : IntegrableOn (fun g => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' g *
      conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E g))
      (canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hL2ψ.integrable_mul hL2φ.star
  have hIΛE : IntegrableOn (fun g => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' g * conj (E g))
      (canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine Integrable.mono' hIEθ.norm
      (hL2ψ.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hEc.aestronglyMeasurable)) ?_
    refine (ae_restrict_iff'₀ hΦnull).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [h2nd x hx, ← hconjθ, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, mul_comm]
  have hadjR := hadj (Real.exp R) hRT E' E hE'c.measurable hEc.measurable hE'B hEB hIΛE hIΛΛ
  have hstepA : ∫ x in canonicalTruncationDomain F α β, lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E x *
        conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x in canonicalTruncationDomain F α β, E x * pseudoEisenstein F p x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    calc ∫ x in canonicalTruncationDomain F α β, lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E x *
          conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∫ x in canonicalTruncationDomain F α β, conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x *
            conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          congr 1; funext x; rw [map_mul, Complex.conj_conj, mul_comm]
      _ = conj (∫ x in canonicalTruncationDomain F α β, lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x *
            conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) := integral_conj
      _ = conj (∫ x in canonicalTruncationDomain F α β, lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x * conj (E x)
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) := by rw [hadjR]
      _ = ∫ x in canonicalTruncationDomain F α β, conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) E' x * conj (E x))
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := integral_conj.symm
      _ = ∫ x in canonicalTruncationDomain F α β, E x * pseudoEisenstein F p x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          refine setIntegral_congr_fun₀ hΦnull (fun x hx => ?_)
          rw [map_mul, Complex.conj_conj, h2nd x hx, hconjθ, mul_comm]

  have hEN : ∀ g, constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 E g = φ g + Mφ g := fun g =>
    constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hαm μ μ hμ hμ s hs φ hφ hφc g

  have hexp : (fun q : RationalTorusUnipotentQuotient F =>
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) E y * p y) q.out) =
      fun q =>
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator (fun _ => (1 : ℂ)) q.out *
          (Set.Iic (Real.exp R)).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F q.out) * (φ q.out * conj (ψ q.out)) +
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator (fun _ => (1 : ℂ)) q.out *
          (Set.Iic (Real.exp R)).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F q.out) * (Mφ q.out * conj (ψ q.out)) -
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator (fun _ => (1 : ℂ)) q.out *
          (Set.Ioi (Real.exp R)).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F q.out) * (φ q.out * conj (Mψ q.out)) -
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator (fun _ => (1 : ℂ)) q.out *
          (Set.Ioi (Real.exp R)).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F q.out) * (Mφ q.out * conj (Mψ q.out)) := by
    funext q
    by_cases hq : q.out ∈ {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      rw [show constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t) E q.out = φ q.out + Mφ q.out from hEN q.out]
      simp only [hpdef, hψRdef]
      by_cases hh : NumberField.AdelicHeight.adelicHeight F q.out ≤ Real.exp R
      · rw [if_pos hh, Set.indicator_of_mem (show NumberField.AdelicHeight.adelicHeight F q.out ∈ Set.Iic (Real.exp R) from hh),
          Set.indicator_of_notMem (show NumberField.AdelicHeight.adelicHeight F q.out ∉ Set.Ioi (Real.exp R) from not_lt.mpr hh)]
        ring
      · rw [if_neg hh, Set.indicator_of_notMem (show NumberField.AdelicHeight.adelicHeight F q.out ∉ Set.Iic (Real.exp R) from hh),
          Set.indicator_of_mem (show NumberField.AdelicHeight.adelicHeight F q.out ∈ Set.Ioi (Real.exp R) from not_le.mp hh), map_neg]
        ring
    · simp only [Set.indicator_of_notMem hq, zero_mul, zero_add, zero_sub, sub_zero, neg_zero]

  obtain ⟨hi₁, he₁⟩ := integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window F hαm
    cIw hcIwT hcIw D D hDm hDm hDF hDF μ μ μ μ hμ hμ hμ hμ hμF hμF hμF hμF s s' φ ψ hφ hψ hφc hψc α β hα
    (Set.Iic (Real.exp R)) measurableSet_Iic
    (lintegral_Iic_inter_Ioi_rpow_lt_top (by linarith) _ (Real.exp_pos R))
  obtain ⟨hi₂, he₂⟩ := integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window F hαm
    cIw hcIwT hcIw D D hDm hDm hDF hDF μ μ μ μ hμ hμ hμ hμ hμF hμF hμF hμF (-s) s' Mφ ψ hMφ hψ hMφc hψc α β hα
    (Set.Iic (Real.exp R)) measurableSet_Iic
    (lintegral_Iic_inter_Ioi_rpow_lt_top (by rw [Complex.neg_re]; linarith) _ (Real.exp_pos R))
  obtain ⟨hi₃, he₃⟩ := integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window F hαm
    cIw hcIwT hcIw D D hDm hDm hDF hDF μ μ μ μ hμ hμ hμ hμ hμF hμF hμF hμF s (-s') φ Mψ hφ hMψ hφc hMψc α β hα
    (Set.Ioi (Real.exp R)) measurableSet_Ioi
    (lintegral_Ioi_inter_Ioi_rpow_lt_top (by rw [Complex.neg_re]; linarith) _ (Real.exp_pos R))
  obtain ⟨hi₄, he₄⟩ := integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window F hαm
    cIw hcIwT hcIw D D hDm hDm hDF hDF μ μ μ μ hμ hμ hμ hμ hμF hμF hμF hμF (-s) (-s') Mφ Mψ hMφ hMψ hMφc hMψc α β hα
    (Set.Ioi (Real.exp R)) measurableSet_Ioi
    (lintegral_Ioi_inter_Ioi_rpow_lt_top (by rw [Complex.neg_re, Complex.neg_re]; linarith) _ (Real.exp_pos R))

  have ht₁ := torus_halfline_lo F αm hαdef hαm μ μ hμ hμ D D hDm hDm hDF hDF α β Cz hCzT hCz V hVT hVl hV s s'
    (by simp only [Complex.add_re, Complex.conj_re]; linarith) R
  have ht₂ := torus_halfline_lo F αm hαdef hαm μ μ hμ hμ D D hDm hDm hDF hDF α β Cz hCzT hCz V hVT hVl hV (-s) s'
    (by simp only [Complex.add_re, Complex.conj_re, Complex.neg_re]; linarith) R
  have ht₃ := torus_halfline_hi F αm hαdef hαm μ μ hμ hμ D D hDm hDm hDF hDF α β Cz hCzT hCz V hVT hVl hV s (-s')
    (by simp only [Complex.add_re, Complex.conj_re, Complex.neg_re]; linarith) R
  have ht₄ := torus_halfline_hi F αm hαdef hαm μ μ hμ hμ D D hDm hDm hDF hDF α β Cz hCzT hCz V hVT hVl hV (-s) (-s')
    (by simp only [Complex.add_re, Complex.conj_re, Complex.neg_re]; linarith) R
  rw [ht₁] at he₁
  rw [ht₂] at he₂
  rw [ht₃] at he₃
  rw [ht₄] at he₄

  refine hstepA.trans ?_
  rw [hUnf, hexp]
  have e1 := integral_sub ((hi₁.add hi₂).sub hi₃) hi₄
  have e2 := integral_sub (hi₁.add hi₂) hi₃
  have e3 := integral_add hi₁ hi₂
  simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3
  rw [e1, e2, e3, he₁, he₂, he₃, he₄]
  simp only [map_neg]
  rw [show -s + (starRingEnd ℂ) s' = -(s - (starRingEnd ℂ) s') by ring,
    show s + -(starRingEnd ℂ) s' = s - (starRingEnd ℂ) s' by ring,
    show -s + -(starRingEnd ℂ) s' = -(s + (starRingEnd ℂ) s') by ring]
  simp only [mul_neg, div_neg, neg_div, neg_neg, Complex.ofReal_mul]
  ring

end MaassSelbergOneHeight

theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hμν : μ = ν)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re) (_hne : s ≠ conj s') (_hlt : s.re < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s') (AutomorphicForm.etaSnd ν αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (c : ℂ) *
        ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ) := by
  exact MaassSelbergOneHeight.oneHeight F α β hα hαβ ΦF

#print axioms solution

end S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re (solution)
