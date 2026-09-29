-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ef6953cf-c7f0-51d3-bd5f-9c9b4a573b72

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_FnTwist
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_setLIntegral_iwasawa_indicator
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_inducedSectionSubmodule_iff LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

namespace FbC3

open NumberField.TateGlobal

lemma window_bound (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    ∫⁻ r in Set.Ioi (0 : ℝ), (Set.Icc α β).indicator (fun _ => (1 : ℝ≥0∞)) (r ^ 2 * y * c) * ENNReal.ofReal r⁻¹
      ≤ ENNReal.ofReal (Real.sqrt β / Real.sqrt α) := by
  set w : ℝ := y * c with hw_def
  have hw : 0 < w := mul_pos hy hc
  have hrw : ∀ r : ℝ, r ^ 2 * y * c = r ^ 2 * w := fun r => by rw [hw_def]; ring
  simp_rw [hrw]
  have hβ : 0 < β := hα.trans hαβ
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hsα : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  set a : ℝ := Real.sqrt α / Real.sqrt w with ha
  set b : ℝ := Real.sqrt β / Real.sqrt w with hb
  have ha0 : 0 < a := by rw [ha]; positivity

  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ),
      (Set.Icc α β).indicator (fun _ => (1 : ℝ≥0∞)) (r ^ 2 * w) * ENNReal.ofReal r⁻¹
        ≤ (Set.Icc a b).indicator (fun _ => ENNReal.ofReal a⁻¹) r := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases hmem : r ^ 2 * w ∈ Set.Icc α β
    · have hra : a ≤ r := by
        rw [ha, div_le_iff₀ hsw]
        have h1 : Real.sqrt α ≤ Real.sqrt (r ^ 2 * w) := Real.sqrt_le_sqrt hmem.1
        rwa [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le] at h1
      have hrb : r ≤ b := by
        rw [hb, le_div_iff₀ hsw]
        have h1 : Real.sqrt (r ^ 2 * w) ≤ Real.sqrt β := Real.sqrt_le_sqrt hmem.2
        rwa [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le] at h1
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hra, hrb⟩), one_mul]
      exact ENNReal.ofReal_le_ofReal ((inv_le_inv₀ hr0 ha0).mpr hra)
    · rw [Set.indicator_of_notMem hmem, zero_mul]
      exact bot_le
  calc ∫⁻ r in Set.Ioi (0 : ℝ), (Set.Icc α β).indicator (fun _ => (1 : ℝ≥0∞)) (r ^ 2 * w) * ENNReal.ofReal r⁻¹
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun _ => ENNReal.ofReal a⁻¹) r :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal a⁻¹ * (volume.restrict (Set.Ioi (0:ℝ))) (Set.Icc a b) :=
        lintegral_indicator_const measurableSet_Icc _
    _ ≤ ENNReal.ofReal a⁻¹ * volume (Set.Icc a b) := by
        gcongr; exact Measure.restrict_le_self
    _ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    _ ≤ ENNReal.ofReal a⁻¹ * ENNReal.ofReal b := by
        gcongr; linarith
    _ = ENNReal.ofReal (Real.sqrt β / Real.sqrt α) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha0.le)]
        congr 1
        rw [ha, hb]
        field_simp

end FbC3

open FbC3 in
theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (T : ℝ) (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞), Measurable F →
        (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, F (x * g) = F g) →
        ∀ (G : ℝ → adelicMaximalCompact K → ℝ≥0∞), Measurable (Function.uncurry G) →
        (∀ (z y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
          F (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) ≤
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K y) *
              G (NumberField.TateGlobal.ideleNorm K y) k) →
        ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β ∩
            {g | T < NumberField.AdelicHeight.adelicHeight K g}, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
          C * ∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹
            ∂volume ∂(maximalCompactHaar K) := by
  classical

  obtain ⟨D, hDm, hDF, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
      K (NumberField.Idele.idelicHaar K)
  obtain ⟨c₀, hc₀, hunf⟩ :=
    AutomorphicForm.exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_setLIntegral_iwasawa_indicator
      K α β hα hαβ
  obtain ⟨V, hV0, hVtop, hpush⟩ :=
    NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi K D hDm hDF
  set L : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt β / Real.sqrt α) with hL
  refine ⟨c₀ * (V * (V * L)), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hc₀ (ENNReal.mul_ne_top hVtop (ENNReal.mul_ne_top hVtop ENNReal.ofReal_ne_top))
  intro T F hF hFinv G hG hFG
  refine (hunf D D hDm hDm hDF hDF T F hF hFinv).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ c₀

  set cK : adelicMaximalCompact K → ℝ := fun k =>
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) with hcK
  have hcKm : Measurable cK :=
    ((NumberField.TateGlobal.continuous_ideleNorm_det K).comp continuous_subtype_val).measurable
  have hcKpos : ∀ k, 0 < cK k := fun k => NumberField.TateGlobal.ideleNorm_pos _
  set φ : ℝ → ℝ → adelicMaximalCompact K → ℝ≥0∞ := fun r y k =>
    (Set.Icc α β).indicator (fun _ => (1 : ℝ≥0∞)) (r ^ 2 * y * cK k) * G y k with hφ

  have hφm : Measurable (fun p : (ℝ × ℝ) × adelicMaximalCompact K => φ p.1.1 p.1.2 p.2) := by
    rw [hφ]
    refine Measurable.mul ?_ (hG.comp (measurable_fst.snd.prodMk measurable_snd))
    refine (measurable_const.indicator measurableSet_Icc).comp ?_
    exact ((measurable_fst.fst.pow_const 2).mul measurable_fst.snd).mul (hcKm.comp measurable_snd)

  have hdet : ∀ (z t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det
        (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)))
        = NumberField.TateGlobal.ideleNorm K z ^ 2 * NumberField.TateGlobal.ideleNorm K t * cK k := by
    intro z t k
    have hdO : Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 (𝓞 K) K) = t := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, diagOne, Matrix.det_fin_two]
    rw [map_mul, map_mul, AutomorphicForm.det_centralScalar K z, hdO, NumberField.TateGlobal.ideleNorm_mul,
      NumberField.TateGlobal.ideleNorm_mul, pow_two, NumberField.TateGlobal.ideleNorm_mul, hcK]
    ring

  have hA : ∀ (z t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      ({g : AdelicGL2 (𝓞 K) K |
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
          {g | T < NumberField.AdelicHeight.adelicHeight K g}).indicator F
          (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
      ≤ φ (NumberField.TateGlobal.ideleNorm K z) (NumberField.TateGlobal.ideleNorm K t) k := by
    intro z t k
    set g := centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K) with hg
    have hnt : 0 < NumberField.TateGlobal.ideleNorm K t := NumberField.TateGlobal.ideleNorm_pos t
    by_cases hmem : g ∈ ({g : AdelicGL2 (𝓞 K) K |
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
          {g | T < NumberField.AdelicHeight.adelicHeight K g})
    · rw [Set.indicator_of_mem hmem]
      have h1 : NumberField.TateGlobal.ideleNorm K z ^ 2 * NumberField.TateGlobal.ideleNorm K t * cK k
          ∈ Set.Icc α β := by
        rw [← hdet]; exact hmem.1
      simp only [hφ]
      rw [Set.indicator_of_mem h1, one_mul]
      calc F g * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ≤ (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t) *
              G (NumberField.TateGlobal.ideleNorm K t) k) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) :=
            mul_le_mul_left (hFG z t k) _
        _ = G (NumberField.TateGlobal.ideleNorm K t) k := by
            rw [ENNReal.ofReal_inv_of_pos hnt, mul_comm, ← mul_assoc,
              ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hnt).ne' ENNReal.ofReal_ne_top, one_mul]
    · rw [Set.indicator_of_notMem hmem, zero_mul]
      exact bot_le

  have hψm : ∀ r : ℝ, Measurable (fun y : ℝ => ∫⁻ k, φ r y k ∂(maximalCompactHaar K)) := by
    intro r
    exact (hφm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).lintegral_prod_right'
  have hAm : Measurable (fun q : ℝ × ℝ => ∫⁻ k, φ q.1 q.2 k ∂(maximalCompactHaar K)) :=
    hφm.lintegral_prod_right'
  have hΨm : Measurable (fun r : ℝ => ∫⁻ y in Set.Ioi (0:ℝ),
      (∫⁻ k, φ r y k ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) := by
    have : Measurable (fun q : ℝ × ℝ => (∫⁻ k, φ q.1 q.2 k ∂(maximalCompactHaar K)) * ENNReal.ofReal q.2⁻¹) :=
      hAm.mul (ENNReal.measurable_ofReal.comp measurable_snd.inv)
    exact this.lintegral_prod_right' (ν := volume.restrict (Set.Ioi (0:ℝ)))
  have hB : ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k,
        ({g : AdelicGL2 (𝓞 K) K |
              NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
            {g | T < NumberField.AdelicHeight.adelicHeight K g}).indicator F
            (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
      ≤ V * (V * ∫⁻ r in Set.Ioi (0:ℝ), (∫⁻ y in Set.Ioi (0:ℝ),
          (∫⁻ k, φ r y k ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) * ENNReal.ofReal r⁻¹) := by
    calc _ ≤ ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k, φ (NumberField.TateGlobal.ideleNorm K z)
            (NumberField.TateGlobal.ideleNorm K t) k
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
          exact lintegral_mono (fun z => lintegral_mono (fun t => lintegral_mono (fun k => hA z t k)))
      _ = ∫⁻ z in D, (V * ∫⁻ y in Set.Ioi (0:ℝ), (∫⁻ k, φ (NumberField.TateGlobal.ideleNorm K z) y k
            ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) ∂(NumberField.Idele.idelicHaar K) := by
          refine lintegral_congr (fun z => ?_)
          exact hpush _ (hψm _)
      _ = V * ∫⁻ z in D, (∫⁻ y in Set.Ioi (0:ℝ), (∫⁻ k, φ (NumberField.TateGlobal.ideleNorm K z) y k
            ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) ∂(NumberField.Idele.idelicHaar K) :=
          lintegral_const_mul' V _ hVtop
      _ = V * (V * ∫⁻ r in Set.Ioi (0:ℝ), (∫⁻ y in Set.Ioi (0:ℝ),
          (∫⁻ k, φ r y k ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) * ENNReal.ofReal r⁻¹) := by
          rw [hpush _ hΨm]

  have hD : ∫⁻ r in Set.Ioi (0:ℝ), (∫⁻ y in Set.Ioi (0:ℝ),
          (∫⁻ k, φ r y k ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) * ENNReal.ofReal r⁻¹
      ≤ L * ∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹ ∂volume ∂(maximalCompactHaar K) := by

    have e1 : ∫⁻ r in Set.Ioi (0:ℝ), (∫⁻ y in Set.Ioi (0:ℝ),
          (∫⁻ k, φ r y k ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) * ENNReal.ofReal r⁻¹
        = ∫⁻ r in Set.Ioi (0:ℝ), ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ k,
            φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹ ∂(maximalCompactHaar K) := by
      refine lintegral_congr (fun r => ?_)
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun y => ?_)
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    rw [e1]

    have m_ryk : Measurable (fun p : (ℝ × ℝ) × adelicMaximalCompact K =>
        φ p.1.1 p.1.2 p.2 * ENNReal.ofReal p.1.2⁻¹ * ENNReal.ofReal p.1.1⁻¹) := by
      refine (hφm.mul (ENNReal.measurable_ofReal.comp measurable_fst.snd.inv)).mul
        (ENNReal.measurable_ofReal.comp measurable_fst.fst.inv)
    have swap1 : ∫⁻ r in Set.Ioi (0:ℝ), ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ k,
            φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹ ∂(maximalCompactHaar K)
        = ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ r in Set.Ioi (0:ℝ), ∫⁻ k,
            φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹ ∂(maximalCompactHaar K) := by
      refine lintegral_lintegral_swap ?_
      exact (m_ryk.lintegral_prod_right').aemeasurable
    rw [swap1]

    have inner : ∀ y ∈ Set.Ioi (0:ℝ), ∫⁻ r in Set.Ioi (0:ℝ), ∫⁻ k,
            φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹ ∂(maximalCompactHaar K)
        ≤ L * ∫⁻ k, G y k * ENNReal.ofReal y⁻¹ ∂(maximalCompactHaar K) := by
      intro y hy
      have hy0 : 0 < y := hy
      have m_rk : Measurable (fun p : ℝ × adelicMaximalCompact K =>
          φ p.1 y p.2 * ENNReal.ofReal y⁻¹ * ENNReal.ofReal p.1⁻¹) :=
        ((hφm.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).mul measurable_const).mul
          (ENNReal.measurable_ofReal.comp measurable_fst.inv)
      rw [lintegral_lintegral_swap m_rk.aemeasurable]
      have hk : ∀ k : adelicMaximalCompact K,
          ∫⁻ r in Set.Ioi (0:ℝ), φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹
            ≤ (G y k * ENNReal.ofReal y⁻¹) * L := by
        intro k
        have mr : Measurable (fun r : ℝ =>
            (Set.Icc α β).indicator (fun _ => (1 : ℝ≥0∞)) (r ^ 2 * y * cK k) * ENNReal.ofReal r⁻¹) :=
          ((measurable_const.indicator measurableSet_Icc).comp
            (((measurable_id.pow_const 2).mul measurable_const).mul measurable_const)).mul
            (ENNReal.measurable_ofReal.comp measurable_inv)
        have e : ∀ r : ℝ, φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹
            = (G y k * ENNReal.ofReal y⁻¹) *
              ((Set.Icc α β).indicator (fun _ => (1 : ℝ≥0∞)) (r ^ 2 * y * cK k) * ENNReal.ofReal r⁻¹) := by
          intro r; simp only [hφ]; ring
        simp_rw [e]
        rw [lintegral_const_mul _ mr]
        exact mul_le_mul_right (window_bound α β hα hαβ y (cK k) hy0 (hcKpos k)) _
      calc ∫⁻ k, (∫⁻ r in Set.Ioi (0:ℝ), φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹) ∂(maximalCompactHaar K)
          ≤ ∫⁻ k, (G y k * ENNReal.ofReal y⁻¹) * L ∂(maximalCompactHaar K) := lintegral_mono hk
        _ = L * ∫⁻ k, G y k * ENNReal.ofReal y⁻¹ ∂(maximalCompactHaar K) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    calc ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ r in Set.Ioi (0:ℝ), ∫⁻ k,
            φ r y k * ENNReal.ofReal y⁻¹ * ENNReal.ofReal r⁻¹ ∂(maximalCompactHaar K)
        ≤ ∫⁻ y in Set.Ioi (0:ℝ), L * ∫⁻ k, G y k * ENNReal.ofReal y⁻¹ ∂(maximalCompactHaar K) :=
          setLIntegral_mono' measurableSet_Ioi inner
      _ = L * ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ k, G y k * ENNReal.ofReal y⁻¹ ∂(maximalCompactHaar K) :=
          lintegral_const_mul' L _ ENNReal.ofReal_ne_top
      _ = L * ∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹ ∂volume ∂(maximalCompactHaar K) := by
          congr 1
          refine lintegral_lintegral_swap ?_
          exact ((hG.comp (measurable_fst.prodMk measurable_snd)).mul
            (ENNReal.measurable_ofReal.comp measurable_fst.inv)).aemeasurable

  calc _ ≤ V * (V * ∫⁻ r in Set.Ioi (0:ℝ), (∫⁻ y in Set.Ioi (0:ℝ),
          (∫⁻ k, φ r y k ∂(maximalCompactHaar K)) * ENNReal.ofReal y⁻¹) * ENNReal.ofReal r⁻¹) := hB
    _ ≤ V * (V * (L * ∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹ ∂volume ∂(maximalCompactHaar K))) := by
        gcongr
    _ = V * (V * L) * ∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹ ∂volume ∂(maximalCompactHaar K) := by
        ring

end S_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul (solution)
