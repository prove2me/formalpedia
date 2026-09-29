-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/726ce4dd-5db1-508a-a32c-d1dc4affbf87

import Theorems.Thm_AutomorphicForm_IsArchTestFactor_exists_isArchTestFactor_nonneg_norm_le
import Theorems.Thm_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset
import Theorems.Thm_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul
import Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
import Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
import Theorems.Thm_AutomorphicForm_exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
import Theorems.Thm_AutomorphicForm_idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_NumberField_exists_finset_forall_ramificationIdx_eq_one
import Theorems.Thm_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange
import Theorems.Thm_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
import Theorems.Thm_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal
import Theorems.Thm_AutomorphicForm_integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
import Theorems.Thm_AutomorphicForm_lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
import Theorems.Thm_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints
import Theorems.Thm_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
import Theorems.Thm_NumberField_exists_forall_haarQuotient_ker_idelicNorm_setOf_idelicNorm_sq_mul_mem_le
import Theorems.Thm_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one
import Theorems.Thm_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex"
p2m_attr_erase "instance" "ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply"
p2m_attr_erase "simp" "Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace PerClassSlack

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure.AutomorphicForm"
open scoped ENNReal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

set_option synthInstance.maxHeartbeats 1600000 in

theorem one_le_semiLocalHaar_doubleCoset (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    1 ≤ semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  have hsub : (fun h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => a⁻¹ * h) ⁻¹' semiLocalIntegralSet K L v ⊆
      semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v := by
    intro h hh
    refine ⟨1 * a, ⟨1, one_mem_semiLocalIntegralSet K L v, a, rfl, rfl⟩, a⁻¹ * h, hh, ?_⟩
    simp only [one_mul, mul_inv_cancel_left]
  have hK : MeasurableSet (semiLocalIntegralSet K L v) := (isOpen_semiLocalIntegralSet K L v).measurableSet
  have hmeas : Measurable (fun h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => a⁻¹ * h) :=
    (continuous_const.mul continuous_id).measurable
  calc (1 : ℝ≥0∞) = semiLocalHaar K L v (semiLocalIntegralSet K L v) :=
        (semiLocalHaar_semiLocalIntegralSet K L v).symm
    _ = (Measure.map (fun h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => a⁻¹ * h) (semiLocalHaar K L v))
          (semiLocalIntegralSet K L v) := by rw [MeasureTheory.map_mul_left_eq_self]
    _ = semiLocalHaar K L v ((fun h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => a⁻¹ * h) ⁻¹'
          semiLocalIntegralSet K L v) := Measure.map_apply hmeas hK
    _ ≤ _ := measure_mono hsub

theorem semiLocalHaar_doubleCoset_lt_top (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) < ∞ := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  exact (((isCompact_semiLocalIntegralSet K L v).mul isCompact_singleton).mul
    (isCompact_semiLocalIntegralSet K L v)).measure_lt_top

theorem log_toReal_semiLocalHaar_doubleCoset_nonneg (v : HeightOneSpectrum (𝓞 K))
    (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    0 ≤ Real.log (semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v)).toReal := by
  refine Real.log_nonneg ?_
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono (semiLocalHaar_doubleCoset_lt_top K L v a).ne (one_le_semiLocalHaar_doubleCoset K L v a)

end PerClassSlack

namespace PerClassReduce

theorem exists_isHaarMeasure_range_of_isClosedEmbedding
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace H] [BorelSpace H]
    (f : G →* H) (hf : Topology.IsClosedEmbedding f) (ν : Measure G) [ν.IsHaarMeasure] :
    IsClosed (f.range : Set H) ∧
    ∃ μ : Measure f.range, μ.IsHaarMeasure ∧ ∀ g : H → ℂ, ∫ a : f.range, g a ∂μ = ∫ a, g (f a) ∂ν := by
  refine ⟨by simpa only [MonoidHom.coe_range] using hf.isClosed_range, ?_⟩
  let e : G ≃* f.range := MonoidHom.ofInjective hf.injective
  have he : Continuous e := hf.continuous.subtype_mk _
  have hval : (fun y : f.range => f (e.symm y)) = fun y : f.range => ((y : f.range) : H) :=
    funext fun y => MonoidHom.apply_ofInjective_symm hf.injective y
  have hes : Continuous e.symm := by
    rw [hf.isInducing.continuous_iff, Function.comp_def, hval]
    exact continuous_subtype_val
  let e' : G ≃ᵐ f.range := (Homeomorph.mk e.toEquiv he hes).toMeasurableEquiv
  refine ⟨Measure.map e ν, e.isHaarMeasure_map ν he hes, fun g => ?_⟩
  have h := integral_map_equiv (μ := ν) e' (fun a : f.range => g a)
  exact h

theorem prod_bound_of_productFormula {ι : Type*} (T' : Finset ι)
    (X CA PA PB nIa : ℝ) (a b C x : ι → ℝ)
    (hX : 0 ≤ X) (hPA : 0 ≤ PA) (hPB : 0 ≤ PB) (hnIa : 0 ≤ nIa)
    (ha : ∀ v ∈ T', 0 ≤ a v) (hb : ∀ v ∈ T', 0 ≤ b v) (hx : ∀ v ∈ T', 0 ≤ x v)
    (hA : PA * nIa ≤ CA * PB ^ ((1:ℝ)/2))
    (hloc : ∀ v ∈ T', a v * x v ≤ C v * b v ^ ((1:ℝ)/2))
    (hPFa : PA * ∏ v ∈ T', a v = 1) (hPFb : PB * ∏ v ∈ T', b v = 1) :
    X * nIa * ∏ v ∈ T', x v ≤ X * CA * ∏ v ∈ T', C v := by
  have hR : 0 ≤ CA * PB ^ ((1:ℝ)/2) := (mul_nonneg hPA hnIa).trans hA
  have hP : ∏ v ∈ T', (a v * x v) ≤ ∏ v ∈ T', (C v * b v ^ ((1:ℝ)/2)) :=
    Finset.prod_le_prod (fun v hv => mul_nonneg (ha v hv) (hx v hv)) hloc
  have key : X * (PA * nIa) * ∏ v ∈ T', (a v * x v) ≤
      X * (CA * PB ^ ((1:ℝ)/2)) * ∏ v ∈ T', (C v * b v ^ ((1:ℝ)/2)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA hX) hP
      (Finset.prod_nonneg fun v hv => mul_nonneg (ha v hv) (hx v hv)) (mul_nonneg hX hR)
  have hb' : ∏ v ∈ T', b v ^ ((1:ℝ)/2) = (∏ v ∈ T', b v) ^ ((1:ℝ)/2) := Real.finsetProd_rpow T' b hb _
  calc X * nIa * ∏ v ∈ T', x v = (PA * ∏ v ∈ T', a v) * (X * nIa * ∏ v ∈ T', x v) := by rw [hPFa, one_mul]
    _ = X * (PA * nIa) * ∏ v ∈ T', (a v * x v) := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ X * (CA * PB ^ ((1:ℝ)/2)) * ∏ v ∈ T', (C v * b v ^ ((1:ℝ)/2)) := key
    _ = X * CA * (∏ v ∈ T', C v) * (PB ^ ((1:ℝ)/2) * ∏ v ∈ T', b v ^ ((1:ℝ)/2)) := by
        rw [Finset.prod_mul_distrib]; ring
    _ = X * CA * (∏ v ∈ T', C v) * ((PB * ∏ v ∈ T', b v) ^ ((1:ℝ)/2)) := by
        rw [hb', Real.mul_rpow hPB (Finset.prod_nonneg hb)]
    _ = X * CA * ∏ v ∈ T', C v := by rw [hPFb, Real.one_rpow, mul_one]

theorem prod_placeConst_eq {ι : Type*} [DecidableEq ι] (T S Ram T' : Finset ι)
    (hT : T ⊆ T') (hS : S \ T ⊆ T') (hR : Ram \ (S ∪ T) ⊆ T')
    (CT m CR : ι → ℝ) (CS : ∀ v : ι, v ∈ S → v ∉ T → ℝ) :
    ∏ v ∈ T', ((if v ∈ T then CT v * m v else 1) * (if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) *
        (if v ∈ Ram \ (S ∪ T) then CR v else 1)) =
      ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) *
        ∏ v ∈ T, CT v) * ∏ v ∈ T, m v := by
  have e1 : ∏ v ∈ T', (if v ∈ T then CT v * m v else 1) = ∏ v ∈ T, (CT v * m v) := by
    rw [← Finset.prod_subset hT (fun v _ hvT => if_neg hvT)]
    exact Finset.prod_congr rfl fun v hv => if_pos hv
  have e2 : ∏ v ∈ T', (if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) =
      ∏ v ∈ S \ T, (if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) :=
    (Finset.prod_subset hS fun v _ hv => dif_neg fun h => hv (Finset.mem_sdiff.mpr h)).symm
  have e3 : ∏ v ∈ T', (if v ∈ Ram \ (S ∪ T) then CR v else 1) = ∏ v ∈ Ram \ (S ∪ T), CR v := by
    rw [← Finset.prod_subset hR (fun v _ hv => if_neg hv)]
    exact Finset.prod_congr rfl fun v hv => if_pos hv
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, e1, e2, e3, Finset.prod_mul_distrib]; ring

theorem final_bound {ι : Type*} [DecidableEq ι] (T S Ram T' : Finset ι)
    (hT : T ⊆ T') (hS : S \ T ⊆ T') (hR : Ram \ (S ∪ T) ⊆ T')
    (CT m CR : ι → ℝ) (CS : ∀ v : ι, v ∈ S → v ∉ T → ℝ)
    (X CA PA PB nIa : ℝ) (a b x : ι → ℝ)
    (hX : 0 ≤ X) (hPA : 0 ≤ PA) (hPB : 0 ≤ PB) (hnIa : 0 ≤ nIa)
    (ha : ∀ v ∈ T', 0 ≤ a v) (hb : ∀ v ∈ T', 0 ≤ b v) (hx : ∀ v ∈ T', 0 ≤ x v)
    (hA : PA * nIa ≤ CA * PB ^ ((1:ℝ)/2))
    (hloc : ∀ v ∈ T', a v * x v ≤
      ((if v ∈ T then CT v * m v else 1) * (if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) *
        (if v ∈ Ram \ (S ∪ T) then CR v else 1)) * b v ^ ((1:ℝ)/2))
    (hPFa : PA * ∏ v ∈ T', a v = 1) (hPFb : PB * ∏ v ∈ T', b v = 1) :
    X * nIa * ∏ v ∈ T', x v ≤ X * CA *
      ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) *
        ∏ v ∈ T, CT v) * ∏ v ∈ T, m v := by
  have h := prod_bound_of_productFormula T' X CA PA PB nIa a b _ x hX hPA hPB hnIa ha hb hx hA hloc hPFa hPFb
  rw [prod_placeConst_eq T S Ram T' hT hS hR CT m CR CS] at h
  simpa only [mul_assoc] using h

theorem slack_bound {ι : Type*} (T : Finset ι) (κ Cvol cG cTi CA CSR : ℝ) (CT X m : ι → ℝ) (AT : ι → ℕ)
    (hκ : 0 ≤ κ) (hCvol : 0 ≤ Cvol) (hcG : 0 ≤ cG) (hcTi : 0 ≤ cTi) (hCA : 0 ≤ CA) (hCSR : 0 ≤ CSR)
    (hCT : ∀ v ∈ T, 0 ≤ CT v) (hm : ∀ v ∈ T, 0 ≤ m v) (hX : ∀ v ∈ T, 1 ≤ X v) :
    κ * (cG * cTi * CA * (CSR * ∏ v ∈ T, CT v * X v ^ AT v) * (∏ v ∈ T, m v) * Cvol) ≤
      κ * Cvol * cG * cTi * CA * (CSR * ∏ v ∈ T, CT v) * ∏ v ∈ T, (m v * X v ^ (∑ u ∈ T, AT u)) := by
  have hT : (∏ v ∈ T, CT v * X v ^ AT v) * ∏ v ∈ T, m v ≤
      (∏ v ∈ T, CT v) * ∏ v ∈ T, (m v * X v ^ (∑ u ∈ T, AT u)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v hv => mul_nonneg (mul_nonneg (hCT v hv)
      (pow_nonneg (zero_le_one.trans (hX v hv)) _)) (hm v hv)) fun v hv => ?_
    have hXA : X v ^ AT v ≤ X v ^ (∑ u ∈ T, AT u) :=
      pow_le_pow_right₀ (hX v hv) (Finset.single_le_sum (fun u _ => Nat.zero_le (AT u)) hv)
    calc CT v * X v ^ AT v * m v = CT v * (m v * X v ^ AT v) := by ring
      _ ≤ CT v * (m v * X v ^ (∑ u ∈ T, AT u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXA (hm v hv)) (hCT v hv)
  have hc : 0 ≤ κ * Cvol * cG * cTi * CA * CSR :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ hCvol) hcG) hcTi) hCA) hCSR
  calc κ * (cG * cTi * CA * (CSR * ∏ v ∈ T, CT v * X v ^ AT v) * (∏ v ∈ T, m v) * Cvol)
      = (κ * Cvol * cG * cTi * CA * CSR) * ((∏ v ∈ T, CT v * X v ^ AT v) * ∏ v ∈ T, m v) := by ring
    _ ≤ (κ * Cvol * cG * cTi * CA * CSR) * ((∏ v ∈ T, CT v) * ∏ v ∈ T, (m v * X v ^ (∑ u ∈ T, AT u))) :=
        mul_le_mul_of_nonneg_left hT hc
    _ = _ := by ring

end PerClassReduce

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArchTestFactor.exists_isArchTestFactor_nonneg_norm_le IsArchTestFactor IsFinTestFactor IsFactorizableTestFn exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset isTopologicalGroup_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf toTensorGL IsSemiLocalTestFn semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet isSemiLocalTestFn_indicator_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar semiLocalHaar_semiLocalIntegralSet sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn IsTwistedOrbitalIntegral archIdentGL semiLocalComponent IsSemiLocalFactorization AdelicGL2 globalPoints centralScalar sigmaAdelicAct exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul tensorArch tensorPlace tensorPlace_apply baseChangeEquiv baseChangeGL baseChangeGLEquiv baseChangeGLEquiv_apply exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2 exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2 exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2 exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL continuous_and_hasCompactSupport_of_isFactorizableTestFn isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one exists_isSemiLocalFactorization_comp_centralScalar_mul exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul"
namespace PerClassReduce
p2m_open "AutomorphicForm"

open scoped TensorProduct.RightActions

noncomputable abbrev nrm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (i : Fin 2) :
    v.adicCompletion K :=
  Algebra.norm (v.adicCompletion K) ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i i)

def LocBound (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (R : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ) : Prop :=
  ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
    (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
    (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
    nrm K L v δ 0 ≠ nrm K L v δ 1 →
  ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
    @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
    τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
  ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I →
    ‖nrm K L v δ 0 - nrm K L v δ 1‖ * ‖I‖ ≤ R δ

end AutomorphicForm.PerClassReduce

namespace AutomorphicForm p2m_export "AutomorphicForm" "IsArchTestFactor.exists_isArchTestFactor_nonneg_norm_le IsArchTestFactor IsFinTestFactor IsFactorizableTestFn exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset isTopologicalGroup_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf toTensorGL IsSemiLocalTestFn semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet isSemiLocalTestFn_indicator_semiLocalIntegralSet semiLocalHaar isHaarMeasure_semiLocalHaar semiLocalHaar_semiLocalIntegralSet sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn IsTwistedOrbitalIntegral archIdentGL semiLocalComponent IsSemiLocalFactorization AdelicGL2 globalPoints centralScalar sigmaAdelicAct exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul tensorArch tensorPlace tensorPlace_apply baseChangeEquiv baseChangeGL baseChangeGLEquiv baseChangeGLEquiv_apply exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2 exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2 exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2 exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL continuous_and_hasCompactSupport_of_isFactorizableTestFn isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one exists_isSemiLocalFactorization_comp_centralScalar_mul exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul" namespace PerClassReduce end AutomorphicForm.PerClassReduce
p2m_open_scoped "AutomorphicForm" in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.PerClassReduce.loc_bound_cases
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S T S₁ Ram : Finset (HeightOneSpectrum (𝓞 K))) (hS₁ : S ∪ T ⊆ S₁)
    (v : HeightOneSpectrum (𝓞 K)) (w₁ : v.Extension (𝓞 L)) (ρv : GL (Fin 2) (w₁.1.adicCompletion L))
    (φv' : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (CTv CRv : ℝ) (CSv : v ∈ S → v ∉ T → ℝ)
    (hCT : AutomorphicForm.PerClassReduce.LocBound K L σ v ((AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)))
      (fun δ' => CTv * (‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2)))
    (hCS : ∀ (hv : v ∈ S) (hvT : v ∉ T),
      AutomorphicForm.PerClassReduce.LocBound K L σ v φv' (fun δ' => CSv hv hvT * ‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ ^ ((1 : ℝ) / 2)))
    (hCR : AutomorphicForm.PerClassReduce.LocBound K L σ v ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (fun δ' => CRv * ‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ ^ ((1 : ℝ) / 2)))
    (hRam : v ∉ Ram → ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (h10 : (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0)
    (h01 : (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0)
    (hreg : AutomorphicForm.PerClassReduce.nrm K L v δv 0 ≠ AutomorphicForm.PerClassReduce.nrm K L v δv 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δv)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δv))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δv) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (c : (L ⊗[K] v.adicCompletion K)ˣ) (I : ℂ)
    (hIvS : v ∈ S₁ → AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δv τ'
      (fun x => (if v ∈ S ∪ T then
          (if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φv')
        else ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))) (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) I)
    (hIvnS : v ∉ S₁ → AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δv τ' ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) I) :
    ‖AutomorphicForm.PerClassReduce.nrm K L v δv 0 - AutomorphicForm.PerClassReduce.nrm K L v δv 1‖ * ‖I‖ ≤
      ((if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) *
        (if v ∈ Ram \ (S ∪ T) then CRv else 1)) *
      ‖AutomorphicForm.PerClassReduce.nrm K L v δv 0 * AutomorphicForm.PerClassReduce.nrm K L v δv 1‖ ^ ((1 : ℝ) / 2) := by
  have hvST : v ∉ Ram \ (S ∪ T) ↔ (v ∈ Ram → v ∈ S ∨ v ∈ T) := by
    simp only [Finset.mem_sdiff, Finset.mem_union, not_and, not_not, imp_iff_not_or]
  by_cases hv1 : v ∈ S₁
  · have hTOI := hIvS hv1
    by_cases hvT : v ∈ T
    ·
      have hC : (if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) * (if v ∈ Ram \ (S ∪ T) then CRv else 1) = CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) := by
        rw [if_pos hvT, dif_neg (fun h => h.2 hvT), if_neg (hvST.mpr fun _ => Or.inr hvT)]; ring
      rw [hC]
      simp only [Finset.mem_union, hvT, or_true, if_true] at hTOI
      refine AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul K L σ v _ (CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2)) ?_ _ _ h10 h01 hreg _ hτ' hτ'1 _ hTOI
      intro δ' h1 h2 h3 τ'' hτ'' hτ''1 I' hI'
      refine (hCT δ' h1 h2 h3 τ'' hτ'' hτ''1 I' hI').trans_eq ?_
      dsimp only [AutomorphicForm.PerClassReduce.nrm]
      rw [Real.mul_rpow (norm_nonneg _) ENNReal.toReal_nonneg]; ring
    · by_cases hvS : v ∈ S
      ·
        have hC : (if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) * (if v ∈ Ram \ (S ∪ T) then CRv else 1) = CSv hvS hvT := by
          rw [if_neg hvT, dif_pos ⟨hvS, hvT⟩, if_neg (hvST.mpr fun _ => Or.inl hvS)]; ring
        rw [hC]
        simp only [Finset.mem_union, hvS, true_or, if_true, hvT, if_false] at hTOI
        exact AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul K L σ v _ (CSv hvS hvT) (hCS hvS hvT) _ _ h10 h01 hreg _ hτ' hτ'1 _ hTOI
      ·
        simp only [Finset.mem_union, hvS, hvT, or_self, if_false] at hTOI
        by_cases hvR : v ∈ Ram
        · have hC : (if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) * (if v ∈ Ram \ (S ∪ T) then CRv else 1) = CRv := by
            rw [if_neg hvT, dif_neg (fun h => hvS h.1), if_pos (Finset.mem_sdiff.mpr ⟨hvR, by simp [hvS, hvT]⟩)]
            ring
          rw [hC]
          exact AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul K L σ v _ CRv hCR _ _ h10 h01 hreg _ hτ' hτ'1 _ hTOI
        · have hC : (if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) * (if v ∈ Ram \ (S ∪ T) then CRv else 1) = 1 := by
            rw [if_neg hvT, dif_neg (fun h => hvS h.1), if_neg (fun h => hvR (Finset.mem_sdiff.mp h).1)]; ring
          rw [hC]
          refine AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul K L σ v _ 1 ?_ _ _ h10 h01 hreg _ hτ' hτ'1 _ hTOI
          intro δ' h1 h2 h3 τ'' hτ'' hτ''1 I' hI'
          exact (AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one K L σ hgen v (hRam hvR) δ' h1 h2 h3 τ'' hτ'' hτ''1 I' hI').trans_eq (one_mul _).symm
  ·
    have hTOI := hIvnS hv1
    have hvS : v ∉ S := fun h => hv1 (hS₁ (Finset.mem_union_left T h))
    have hvT : v ∉ T := fun h => hv1 (hS₁ (Finset.mem_union_right S h))
    by_cases hvR : v ∈ Ram
    · have hC : (if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) * (if v ∈ Ram \ (S ∪ T) then CRv else 1) = CRv := by
        rw [if_neg hvT, dif_neg (fun h => hvS h.1), if_pos (Finset.mem_sdiff.mpr ⟨hvR, by simp [hvS, hvT]⟩)]; ring
      rw [hC]
      exact hCR _ h10 h01 hreg _ hτ' hτ'1 _ hTOI
    · have hC : (if v ∈ T then CTv * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₁.1 ρv))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) else 1) * (if h : v ∈ S ∧ v ∉ T then CSv h.1 h.2 else 1) * (if v ∈ Ram \ (S ∪ T) then CRv else 1) = 1 := by
        rw [if_neg hvT, dif_neg (fun h => hvS h.1), if_neg (fun h => hvR (Finset.mem_sdiff.mp h).1)]; ring
      rw [hC, one_mul]
      exact AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one K L σ hgen v (hRam hvR) _ h10 h01 hreg _ hτ' hτ'1 _ hTOI

p2m_open_scoped "AutomorphicForm" in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.PerClassReduce.norm_twistedOrbital_translate_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (νA : Measure (InfiniteAdeleRing K)ˣ) [νA.IsHaarMeasure]
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (cG : ℝ) (hcG : 0 < cG)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v)
          (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) *
              ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = 0) →
          ∫ x, F x ∂μ = cG * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t)
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (hτac : ∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
            g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τa =
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA))
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (Ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (CA : ℝ) (hCA : 0 ≤ CA)
    (hA :
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
        AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
      ∀ (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L δ))
          (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L δ))),
        @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L δ)) τa →
        (∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
          ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
              g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τa =
            ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
              g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA)) →
      ∀ (c : (InfiniteAdeleRing L)ˣ) (I : ℂ),
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν
          (AutomorphicForm.tensorArch K L δ) τa
          ((fun g : GL (Fin 2) (InfiniteAdeleRing L) => Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)) ∘
            AutomorphicForm.archIdentGL K L) I →
        (∏ v : InfinitePlace K,
            v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) - Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^
              v.mult) * ‖I‖ ≤
          CA * (∏ v : InfinitePlace K,
            v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^
              v.mult) ^ ((1 : ℝ) / 2))
    (CT : HeightOneSpectrum (𝓞 K) → ℝ) (hCT0 : ∀ v, 0 ≤ CT v)
    (hCT : ∀ (v : HeightOneSpectrum (𝓞 K)),
      AutomorphicForm.PerClassReduce.LocBound K L σ v ((AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
              AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)))
        (fun δ' => CT v * (‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ * (AutomorphicForm.semiLocalHaar K L v (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
              AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2)))
    (CS : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S → v ∉ T → ℝ) (hCS0 : ∀ v hv hvT, 0 ≤ CS v hv hvT)
    (hCS : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) (hvT : v ∉ T),
      AutomorphicForm.PerClassReduce.LocBound K L σ v (φS' v) (fun δ' => CS v hv hvT * ‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ ^ ((1 : ℝ) / 2)))
    (CR : HeightOneSpectrum (𝓞 K) → ℝ) (hCR0 : ∀ v, 0 ≤ CR v)
    (hCR : ∀ v : HeightOneSpectrum (𝓞 K),
      AutomorphicForm.PerClassReduce.LocBound K L σ v ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        (fun δ' => CR v * ‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ ^ ((1 : ℝ) / 2)))
    (Ram : Finset (HeightOneSpectrum (𝓞 K)))
    (hRam : ∀ v ∉ Ram, ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (φp : AdelicGL2 (𝓞 L) L → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfactp : AutomorphicForm.IsSemiLocalFactorization K L (S ∪ T) φp Ψ φf'
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
              AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
        else φS' v))
    (w : (AdeleRing (𝓞 L) L)ˣ) (Iw : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
        ((fun g : AdelicGL2 (𝓞 L) L => φp (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
          AutomorphicForm.baseChangeGL K L) Iw) :
    ‖Iw‖ ≤ cG * cT⁻¹ * CA *
      ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) *
        ∏ v ∈ T, CT v) *
      ∏ v ∈ T, (AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v *
                {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) := by
  classical

  have hδreg := AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
    K L σ hgen t ht₁ ht₂ hreg δ hδ
  have hσ : σ ^ Module.finrank K L = 1 := by
    rw [← IsGalois.card_aut_eq_finrank K L]; exact pow_card_eq_one'

  obtain ⟨S₁, hS₁, hfw⟩ :=
    AutomorphicForm.exists_isSemiLocalFactorization_comp_centralScalar_mul K L (S ∪ T) φp Ψ φf' _ hfactp w
  rcases AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
      K L σ hσ μ hμ ν cG hG δ hδreg τ hτ τa hτa τf hτf hτf1 cT hcT hT S₁ _ _ _ _ hfw Iw hI with
    ⟨h0, -⟩ | ⟨S₂, hS₂, Ia, Iv, hIa, hIvS, hIvnS, hprod⟩
  · rw [h0, norm_zero]
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcG.le (inv_nonneg.mpr hcT.le)) hCA) ?_)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => ?_) (Finset.prod_nonneg fun v _ => hCR0 v))
      (Finset.prod_nonneg fun v _ => hCT0 v)
    split_ifs with h
    · exact hCS0 v h.1 h.2
    · exact zero_le_one

  have hdet : Matrix.det (t : Matrix (Fin 2) (Fin 2) L) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det t).ne_zero
  have hα : (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h; apply hdet; rw [Matrix.det_fin_two, h, ht₂]; ring
  have hβ : (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
    intro h; apply hdet; rw [Matrix.det_fin_two, h, ht₂]; ring
  have hNne : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    intro h
    apply hreg
    have hβN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    have hmul : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) *
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
      rw [← map_mul, div_mul_cancel₀ _ hβ]
    rw [h] at hmul
    exact (mul_eq_right₀ hβN).mp hmul.symm
  have hx : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) - Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := sub_ne_zero.mpr hNne
  have hy : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 :=
    mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hα) (Algebra.norm_ne_zero_iff.mpr hβ)
  obtain ⟨Tx, hTx⟩ :=
    NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one K _ hx
  obtain ⟨Ty, hTy⟩ :=
    NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one K _ hy

  have hIw := hprod (S₂ ∪ Ram ∪ (Tx ∪ Ty)) (Finset.subset_union_left.trans Finset.subset_union_left)
  have hST : S ∪ T ⊆ (S₂ ∪ Ram ∪ (Tx ∪ Ty)) :=
    (hS₁.trans hS₂).trans (Finset.subset_union_left.trans Finset.subset_union_left)

  have hA' := hA t ht₁ ht₂ hreg δ hδ τa hτa hτac _ Ia hIa

  have hPF := AutomorphicForm.norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints K L t δ hδ
  have hent : ∀ i j : Fin 2, (t : Matrix (Fin 2) (Fin 2) L) i j = 0 →
      ((δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j = 0 := by
    intro i j hij
    have h : AutomorphicForm.baseChangeEquiv K L
        (((δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j) =
        algebraMap L (AdeleRing (𝓞 L) L) ((t : Matrix (Fin 2) (Fin 2) L) i j) :=
      congrArg (fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) hδ
    rw [hij, map_zero] at h
    exact (map_eq_zero_iff _ (AutomorphicForm.baseChangeEquiv K L).injective).mp h
  have h10 : ∀ v : HeightOneSpectrum (𝓞 K),
      ((AutomorphicForm.tensorPlace K L v δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 := fun v => by
    rw [AutomorphicForm.tensorPlace_apply, hent 1 0 ht₁, map_zero]
  have h01 : ∀ v : HeightOneSpectrum (𝓞 K),
      ((AutomorphicForm.tensorPlace K L v δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 := fun v => by
    rw [AutomorphicForm.tensorPlace_apply, hent 0 1 ht₂, map_zero]
  have hregv : ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 0 ≠ AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 1 := fun v => by
    dsimp only [AutomorphicForm.PerClassReduce.nrm]
    rw [(hPF 0 0).1 v, (hPF 1 1).1 v]
    exact fun h => hNne ((algebraMap K (v.adicCompletion K)).injective h)
  have hPFa : (∏ v : InfinitePlace K, v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) - Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^ v.mult) * ∏ v ∈ (S₂ ∪ Ram ∪ (Tx ∪ Ty)), (fun v : HeightOneSpectrum (𝓞 K) => ‖AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 0 - AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 1‖) v = 1 := by
    refine (congrArg _ (Finset.prod_congr rfl fun v _ => ?_)).trans
      (hTx _ (Finset.subset_union_left.trans Finset.subset_union_right))
    dsimp only [AutomorphicForm.PerClassReduce.nrm]
    rw [(hPF 0 0).1 v, (hPF 1 1).1 v, ← map_sub]
  have hPFb : (∏ v : InfinitePlace K, v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^ v.mult) * ∏ v ∈ (S₂ ∪ Ram ∪ (Tx ∪ Ty)), (fun v : HeightOneSpectrum (𝓞 K) => ‖AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 0 * AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 1‖) v = 1 := by
    refine (congrArg _ (Finset.prod_congr rfl fun v _ => ?_)).trans
      (hTy _ (Finset.subset_union_right.trans Finset.subset_union_right))
    dsimp only [AutomorphicForm.PerClassReduce.nrm]
    rw [(hPF 0 0).1 v, (hPF 1 1).1 v, ← map_mul]

  have key := PerClassReduce.final_bound T S Ram (S₂ ∪ Ram ∪ (Tx ∪ Ty))
    (Finset.subset_union_right.trans hST) (Finset.sdiff_subset.trans (Finset.subset_union_left.trans hST))
    (Finset.sdiff_subset.trans (Finset.subset_union_right.trans Finset.subset_union_left))
    CT (fun v => (AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v *
                {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                AutomorphicForm.semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2)) CR CS (cG * cT⁻¹) CA (∏ v : InfinitePlace K, v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) - Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^ v.mult) (∏ v : InfinitePlace K, v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^ v.mult) ‖Ia‖ (fun v : HeightOneSpectrum (𝓞 K) => ‖AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 0 - AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 1‖) (fun v : HeightOneSpectrum (𝓞 K) => ‖AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 0 * AutomorphicForm.PerClassReduce.nrm K L v (AutomorphicForm.tensorPlace K L v δ) 1‖) (fun v => ‖Iv v‖)
    (mul_nonneg hcG.le (inv_nonneg.mpr hcT.le))
    (Finset.prod_nonneg fun v _ => pow_nonneg (apply_nonneg _ _) _)
    (Finset.prod_nonneg fun v _ => pow_nonneg (apply_nonneg _ _) _) (norm_nonneg _)
    (fun v _ => norm_nonneg _) (fun v _ => norm_nonneg _) (fun v _ => norm_nonneg _) hA'
    (fun v _ => AutomorphicForm.PerClassReduce.loc_bound_cases K L σ hgen S T S₁ Ram hS₁ v (ws v) (ρ v) (φS' v)
      (CT v) (CR v) (CS v) (hCT v) (hCS v) (hCR v) (hRam v) _ (h10 v) (h01 v) (hregv v) _ (hτf v) (hτf1 v)
      _ (Iv v) (hIvS v) (hIvnS v))
    hPFa hPFb
  rw [hIw]
  simp only [norm_mul, norm_inv, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcG, abs_of_pos hcT]
  exact le_trans (le_of_eq (by ring)) key

p2m_open_scoped "AutomorphicForm" in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.PerClassReduce.per_class
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νK : Measure (AdeleRing (𝓞 K) K)ˣ) [νK.IsHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (νA : Measure (InfiniteAdeleRing K)ˣ) [νA.IsHaarMeasure]
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν)
    (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (hφS : ∀ v ∈ S, v ∉ T → AutomorphicForm.IsSemiLocalTestFn K L v (φS v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≤
        ENNReal.ofReal (C * ∏ v ∈ T,
          ((AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A)) := by
  classical

  obtain ⟨Ψ, hΨ, hΨ0, hΨdom⟩ :=
    AutomorphicForm.IsArchTestFactor.exists_isArchTestFactor_nonneg_norm_le L φa hφa

  let φSabs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ :=
    fun v x => ((‖φS v x‖ : ℝ) : ℂ)
  have hole_φSabs : ∀ v ∈ S, v ∉ T → AutomorphicForm.IsSemiLocalTestFn K L v (φSabs v) := by
    intro v hv hvT
    obtain ⟨hlc, hcs⟩ := hφS v hv hvT
    exact ⟨hlc.comp (fun c : ℂ => ((‖c‖ : ℝ) : ℂ)), hcs.comp_left (g := fun c : ℂ => ((‖c‖ : ℝ) : ℂ)) (by simp)⟩

  obtain ⟨cτ, hcτ, hτ⟩ :=
    AutomorphicForm.exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2
      K L σ hgen νK
  have hP1a :=
    AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2
      K L σ hgen νA
  obtain ⟨cT, hcT, hT⟩ :=
    AutomorphicForm.exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
      K L σ hgen νK νA cτ hcτ
  obtain ⟨cG, hcG, hG⟩ :=
    AutomorphicForm.exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure K L μ hμ ν hν
  obtain ⟨cμ, hcμ, hμc⟩ :=
    AutomorphicForm.exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar K L μ hμ
  obtain ⟨cH, hcH, hHc'⟩ :=
    AutomorphicForm.exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2
      K L νZL D σ hgen H hHc hH μH νK

  let βu : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom
  let AK : Subgroup (AdeleRing (𝓞 L) L)ˣ := MonoidHom.range βu
  have hEmb := PerClassReduce.exists_isHaarMeasure_range_of_isClosedEmbedding βu
    (M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange K L) νK
  have hole_AKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ) := hEmb.1
  have hole_AK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a := by
    intro z
    simp only [AK, MonoidHom.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  have hole_μAK : ∃ μAK : Measure AK, μAK.IsHaarMeasure ∧
      ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
        ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
          ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νK := hEmb.2
  obtain ⟨μAK, iμAK, hμAK⟩ := hole_μAK
  let N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker
  have hole_N1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ) := by
    haveI : T2Space (AdeleRing (𝓞 K) K)ˣ := Units.isEmbedding_embedProduct.t2Space
    have hc : Continuous (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm :=
      Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)
    simpa only [N1, MonoidHom.coe_ker] using isClosed_singleton.preimage hc
  have hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1 := fun z => MonoidHom.mem_ker
  have hole_μN : ∃ μN : Measure N1, μN.IsHaarMeasure := by
    haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
    haveI : LocallyCompactSpace N1 := hole_N1c.isClosedEmbedding_subtypeVal.locallyCompactSpace
    exact ⟨Measure.haar, Measure.isHaarMeasure_haarMeasure _⟩
  obtain ⟨μN, iμN⟩ := hole_μN
  obtain ⟨cN, hcN, hNc⟩ :=
    M4aHerbrand.IdeleGaloisDescent.exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
      K L νZL D σ hgen AK hole_AKc hole_AK μAK N1 hole_N1c hN1 μN

  obtain ⟨C₀, hC₀c, hsupp⟩ :=
    AutomorphicForm.exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
      K L S Ψ φSabs T ws
  obtain ⟨Cvol, hCvol, hvol⟩ :=
    NumberField.exists_forall_haarQuotient_ker_idelicNorm_setOf_idelicNorm_sq_mul_mem_le K L νZL N1 hole_N1c hN1 μN C₀ hC₀c
  obtain ⟨CA, hCA, hA⟩ :=
    AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul
      K L σ hgen νA ν hν Ψ hΨ

  have hB3 := fun v : HeightOneSpectrum (𝓞 K) =>
    AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset
      K L σ hgen v (ws v)
  choose CT hCT0 AT hCT using hB3
  have hB5S := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) (hvT : v ∉ T) =>
    AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn
      K L σ hgen v (φSabs v) (hole_φSabs v hv hvT)
  choose CS hCS0 hCS using hB5S
  have hole_unitTestFn : ∀ v : HeightOneSpectrum (𝓞 K),
      AutomorphicForm.IsSemiLocalTestFn K L v ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) :=
    fun v => AutomorphicForm.isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
  have hB5R := fun v : HeightOneSpectrum (𝓞 K) =>
    AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn
      K L σ hgen v _ (hole_unitTestFn v)
  choose CR hCR0 hCR using hB5R
  have hole_Ram : ∃ Ram : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ Ram,
      ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1 := by
    obtain ⟨S₀, hS₀⟩ := NumberField.exists_finset_forall_ramificationIdx_eq_one K L
    exact ⟨S₀, fun v hv w' hw' => hS₀ w' (hw' ▸ hv)⟩
  obtain ⟨Ram, hRam⟩ := hole_Ram

  let κ : ℝ := cN * cτ / (cH * cμ)
  let Cfin : ℝ := (∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) * ∏ v ∈ T, CT v
  let Cbig : ℝ := κ * Cvol * cG * cT⁻¹ * CA * Cfin
  have hκ : 0 ≤ κ := div_nonneg (mul_nonneg hcN.le hcτ.le) (mul_nonneg hcH.le hcμ.le)
  have hCfin : 0 ≤ Cfin := by
    refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => ?_) (Finset.prod_nonneg fun v _ => hCR0 v))
      (Finset.prod_nonneg fun v _ => hCT0 v)
    split_ifs with h
    · exact hCS0 v h.1 h.2
    · exact zero_le_one
  have hole_Cbig_nonneg : 0 ≤ Cbig :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ hCvol) hcG.le)
      (inv_nonneg.mpr hcT.le)) hCA) hCfin
  refine ⟨Cbig, hole_Cbig_nonneg, ∑ v ∈ T, AT v, ?_⟩
  intro ρ φ φf hfact t ht₁ ht₂ hreg

  let δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
    (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.globalPoints (𝓞 L) L t)
  have hole_δ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t := by
    show AutomorphicForm.baseChangeGL K L ((AutomorphicForm.baseChangeGLEquiv K L).symm _) = _
    rw [← AutomorphicForm.baseChangeGLEquiv_apply]
    exact (AutomorphicForm.baseChangeGLEquiv K L).apply_symm_apply _
  obtain ⟨τ, hτH, hτc⟩ := hτ t ht₁ ht₂ hreg δ hole_δ
  obtain ⟨τa, hτaH, hτac⟩ := hP1a t ht₁ ht₂ hreg δ hole_δ
  obtain ⟨τf, hτfH, hτf1⟩ :=
    AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one K L σ δ
  have hTδ := hT t ht₁ ht₂ hreg δ hole_δ τ hτH hτc τa hτaH hτac τf hτfH hτf1

  let φfabs : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ := fun h => ((‖φf h‖ : ℝ) : ℂ)
  let φp : AdelicGL2 (𝓞 L) L → ℂ :=
    fun g => Ψ (AdelicLevel.glArch (𝓞 L) L g) * φfabs (AdelicLevel.glFin (𝓞 L) L g)
  have hφfabs : AutomorphicForm.IsFinTestFactor L φfabs :=
    ⟨hfact.2.1.1.comp (fun c : ℂ => ((‖c‖ : ℝ) : ℂ)),
      hfact.2.1.2.comp_left (g := fun c : ℂ => ((‖c‖ : ℝ) : ℂ)) (by simp)⟩
  have hole_factp : IsSemiLocalFactorization K L (S ∪ T) φp Ψ φfabs
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
              semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
        else φSabs v) := by
    refine ⟨hΨ, hφfabs, ?_, ?_, ?_, fun _ => rfl⟩
    · intro v hv
      by_cases hvT : v ∈ T
      · simpa only [if_pos hvT] using hfact.2.2.1 v hv
      · simp only [if_neg hvT]
        exact hole_φSabs v ((Finset.mem_union.1 hv).elim id fun h => absurd h hvT) hvT
    · intro h hh
      rw [show φfabs h = ((‖φf h‖ : ℝ) : ℂ) from rfl, hfact.2.2.2.1 h hh, norm_prod, Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      by_cases hvT : v ∈ T
      · simp only [if_pos hvT, Set.indicator_apply]
        split_ifs <;> simp
      · simp only [if_neg hvT, φSabs]
    · intro h hh
      simp only [φfabs, hfact.2.2.2.2.1 h hh, norm_zero, Complex.ofReal_zero]
  have hφpfact : AutomorphicForm.IsFactorizableTestFn L φp := ⟨Ψ, φfabs, hΨ, hφfabs, fun _ => rfl⟩
  obtain ⟨hole_φp_cont, hole_φp_supp⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φp hφpfact
  have hole_φp_nonneg : ∀ g : AdelicGL2 (𝓞 L) L, 0 ≤ (φp g).re ∧ (φp g).im = 0 := by
    intro g
    obtain ⟨h1, h2⟩ := hΨ0 (AdelicLevel.glArch (𝓞 L) L g)
    simp only [φp, φfabs, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h2,
      mul_zero, sub_zero, zero_mul, add_zero]
    exact ⟨mul_nonneg h1 (norm_nonneg _), trivial⟩
  have hole_dom : ∀ g : AdelicGL2 (𝓞 L) L, ‖φ g‖ ≤ (φp g).re := by
    intro g
    obtain ⟨h1, h2⟩ := hΨ0 (AdelicLevel.glArch (𝓞 L) L g)
    rw [hfact.2.2.2.2.2 g, norm_mul]
    simp only [φp, φfabs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right (hΨdom _) (norm_nonneg _)

  have hole_mono : (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
          (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≤
      (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
          (∫⁻ z, ENNReal.ofReal ‖φp (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) := by
    refine lintegral_mono fun q => lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    exact (hole_dom _).trans (Complex.re_le_norm _)

  have hole_ξ1c : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      (((1 : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const
  have hξ1σ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      (1 : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ =
        (1 : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) ⟨z, Subgroup.mem_top z⟩ := fun _ => rfl
  have hintξ :=
    AutomorphicForm.integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal
      K L νZL D σ hgen 1 hole_ξ1c hξ1σ (fun _ _ => rfl) H hHc hH μH t ht₁ ht₂ hreg φp hole_φp_cont hole_φp_supp
  have hole_int : Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
        (∫ z, φp (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by
    simpa only [MonoidHom.one_apply, Units.val_one, one_mul] using hintξ
  have hbridge :=
    AutomorphicForm.lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
      K L νZL D σ hgen H hHc hH μH t ht₁ ht₂ hreg φp hole_φp_cont hole_φp_supp hole_φp_nonneg hole_int

  have hole_Iex : ∃ I : (AdeleRing (𝓞 L) L)ˣ → ℂ, ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
        ((fun g : AdelicGL2 (𝓞 L) L => φp (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
          AutomorphicForm.baseChangeGL K L) (I w) := by
    have hδreg := AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
      K L σ hgen t ht₁ ht₂ hreg δ hole_δ
    have hcs : ∀ w : (AdeleRing (𝓞 L) L)ˣ, HasCompactSupport
        ((fun g : AdelicGL2 (𝓞 L) L => φp (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
          AutomorphicForm.baseChangeGL K L) := by
      intro w
      have h := hole_φp_supp.comp_homeomorph
        ((AutomorphicForm.baseChangeGLEquiv K L).toHomeomorph.trans
          (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 L) L w)))
      exact h
    have hsec := fun w : (AdeleRing (𝓞 L) L)ˣ =>
      AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
        K L σ δ hδreg τ hτH _ (hcs w)
    choose sw hsw using hsec
    exact ⟨fun w => ∫ x, ((fun g : AdelicGL2 (𝓞 L) L => φp (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
          AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
            ((sw w x : ℝ) : ℂ) ∂μ,
      fun w => ⟨sw w, hsw w, rfl⟩⟩
  obtain ⟨I, hI⟩ := hole_Iex

  have hunf :=
    (AutomorphicForm.integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
      K L νZL D σ hgen 1 hole_ξ1c hξ1σ H hHc hH μH μ hμ cμ hcμ hμc νK cH hcH hHc' cτ hcτ AK hole_AKc hole_AK μAK hμAK
      N1 hole_N1c hN1 μN cN hcN hNc t ht₁ ht₂ hreg δ hole_δ τ hτH hτc φp hole_φp_cont hole_φp_supp).1 I hI hintξ

  obtain ⟨b, hb⟩ := hsupp ρ φp φfabs hole_factp
  have hole_Isupp : ∀ w : (AdeleRing (𝓞 L) L)ˣ, I w ≠ 0 →
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w ^ 2 *
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
            (Matrix.GeneralLinearGroup.det (AutomorphicForm.baseChangeGL K L δ)) * b) ∈ C₀ := by
    intro w hw
    obtain ⟨sw, -, hIw⟩ := hI w
    have hex : ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
        φp (AutomorphicForm.centralScalar (𝓞 L) L w * AutomorphicForm.baseChangeGL K L
          (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x)) ≠ 0 := by
      by_contra h
      push Not at h
      apply hw
      rw [hIw]
      simp only [Function.comp_apply, h, zero_mul, integral_zero]
    obtain ⟨x, hx⟩ := hex
    have hmem := hb _ hx
    rwa [AutomorphicForm.idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL K L σ w δ x,
      mul_assoc] at hmem
  have hvolδ := hvol ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
            (Matrix.GeneralLinearGroup.det (AutomorphicForm.baseChangeGL K L δ)) * b)

  have hX1 : ∀ v : HeightOneSpectrum (𝓞 K), 1 ≤ (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) := fun v => by
    have := PerClassSlack.log_toReal_semiLocalHaar_doubleCoset_nonneg K L v
      (semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))
    linarith
  have hCT0' : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ CT v * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ AT v :=
    fun v => mul_nonneg (hCT0 v) (pow_nonneg (zero_le_one.trans (hX1 v)) _)
  have hCT' : ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.PerClassReduce.LocBound K L σ v
      ((semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
          semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)))
      (fun δ' => CT v * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ AT v *
        (‖AutomorphicForm.PerClassReduce.nrm K L v δ' 0 * AutomorphicForm.PerClassReduce.nrm K L v δ' 1‖ *
          (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2)) := by
    intro v δ' h1 h2 h3 τ'' hτ'' hτ''1 I' hI'
    refine (hCT v (ρ v) δ' h1 h2 h3 τ'' hτ'' hτ''1 I' hI').trans_eq ?_
    dsimp only [AutomorphicForm.PerClassReduce.nrm]
    ring
  have hCSR : 0 ≤ (∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) := by
    refine mul_nonneg (Finset.prod_nonneg fun v _ => ?_) (Finset.prod_nonneg fun v _ => hCR0 v)
    split_ifs with h
    · exact hCS0 v h.1 h.2
    · exact zero_le_one

  have hole_Ibound : ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      ‖I w‖ ≤ cG * cT⁻¹ * CA * ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) *
          ∏ v ∈ T, CT v * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ AT v) *
        ∏ v ∈ T, (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) := by
    intro w
    exact AutomorphicForm.PerClassReduce.norm_twistedOrbital_translate_le K L σ hgen S T ws ρ νA μ hμ ν cG hcG hG
      t ht₁ ht₂ hreg δ hole_δ τ hτH τa hτaH τf hτfH hτf1 hτac cT hcT hTδ Ψ φSabs CA hCA hA
      (fun v => CT v * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ AT v) hCT0' hCT'
      CS hCS0 hCS CR hCR0 hCR Ram hRam φp φfabs hole_factp w (I w) (hI w)

  have hole_final : (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
          (∫⁻ z, ENNReal.ofReal ‖φp (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≤
      ENNReal.ofReal (Cbig * ∏ v ∈ T, ((AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ (∑ u ∈ T, AT u))) := by
    rw [hbridge]
    apply ENNReal.ofReal_le_ofReal
    have hBnn : 0 ≤ (cG * cT⁻¹ * CA * ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) *
          ∏ v ∈ T, CT v * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ AT v) *
        ∏ v ∈ T, (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcG.le (inv_nonneg.mpr hcT.le)) hCA)
        (mul_nonneg hCSR (Finset.prod_nonneg fun v _ => hCT0' v)))
        (Finset.prod_nonneg fun v _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    have hIE : ∀ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ, wq ∉ {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ |
        (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 *
          ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
              (Matrix.GeneralLinearGroup.det (AutomorphicForm.baseChangeGL K L δ)) * b) ∈ C₀} → I wq.out = 0 :=
      fun wq hwq => by_contra fun h => hwq (hole_Isupp _ h)
    have hEfin : HaarQuotient.measure νZL N1 μN {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ |
        (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 *
          ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
              (Matrix.GeneralLinearGroup.det (AutomorphicForm.baseChangeGL K L δ)) * b) ∈ C₀} < ⊤ := lt_of_le_of_lt hvolδ ENNReal.ofReal_lt_top
    have hint : ‖∫ wq, I wq.out ∂(HaarQuotient.measure νZL N1 μN)‖ ≤ (cG * cT⁻¹ * CA * ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v) *
          ∏ v ∈ T, CT v * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ AT v) *
        ∏ v ∈ T, (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2)) * Cvol := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hIE]
      exact (norm_setIntegral_le_of_norm_le_const hEfin fun wq _ => hole_Ibound _).trans
        (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hCvol hvolδ) hBnn)
    have h2 := hunf.2
    simp only [MonoidHom.one_apply, Units.val_one, one_mul] at h2
    rw [h2]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ]
    refine (mul_le_mul_of_nonneg_left hint hκ).trans ?_
    simp only [Cbig, Cfin]
    exact PerClassReduce.slack_bound T κ Cvol cG cT⁻¹ CA ((∏ v ∈ S \ T, if h : v ∈ S ∧ v ∉ T then CS v h.1 h.2 else 1) * (∏ v ∈ Ram \ (S ∪ T), CR v)) CT
      (fun v => (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) (fun v => (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2)) AT
      hκ hCvol hcG.le (inv_nonneg.mpr hcT.le) hCA hCSR (fun v _ => hCT0 v)
      (fun v _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) (fun v _ => hX1 v)
  exact le_trans hole_mono hole_final

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure.AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≤
        ENNReal.ofReal (C * ∏ v ∈ T,
          ((AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A)) := by
  intro T ws
  classical

  letI mK : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := borel _
  haveI bK : BorelSpace (AdeleRing (𝓞 K) K)ˣ := ⟨rfl⟩
  letI mA : MeasurableSpace (InfiniteAdeleRing K)ˣ := borel _
  haveI bA : BorelSpace (InfiniteAdeleRing K)ˣ := ⟨rfl⟩
  have hole_haarK : ∃ νK : Measure (AdeleRing (𝓞 K) K)ˣ, νK.IsHaarMeasure := by
    haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
    exact ⟨Measure.haar, Measure.isHaarMeasure_haarMeasure _⟩
  obtain ⟨νK, iνK⟩ := hole_haarK
  have hole_haarA : ∃ νA : Measure (InfiniteAdeleRing K)ˣ, νA.IsHaarMeasure := by
    haveI : LocallyCompactSpace (InfiniteAdeleRing K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
    exact ⟨Measure.haar, Measure.isHaarMeasure_haarMeasure _⟩
  obtain ⟨νA, iνA⟩ := hole_haarA
  have hole_haarGL : ∃ μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)),
      @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ := by
    letI := AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
    haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
    haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
    haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (AdeleRing (𝓞 K) K)
    exact ⟨Measure.haar, Measure.isHaarMeasure_haarMeasure _⟩
  obtain ⟨μ, hμ⟩ := hole_haarGL
  have hole_haarGLarch : ∃ ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)),
      @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
        (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν := by
    letI := AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
    haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
    exact ⟨Measure.haar, Measure.isHaarMeasure_haarMeasure _⟩
  obtain ⟨ν, hν⟩ := hole_haarGLarch

  by_cases hpre : AutomorphicForm.IsArchTestFactor L φa ∧
      ∀ v ∈ S, v ∉ T → AutomorphicForm.IsSemiLocalTestFn K L v (φS v)
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro ρ φ φf hfact
    have hole_vac : AutomorphicForm.IsArchTestFactor L φa ∧
        ∀ v ∈ S, v ∉ T → AutomorphicForm.IsSemiLocalTestFn K L v (φS v) := by
      refine ⟨hfact.1, fun v hv hvT => ?_⟩
      have h := hfact.2.2.1 v (Finset.mem_union_left T hv)
      simp only [if_neg hvT] at h
      exact h
    exact absurd hole_vac hpre
  obtain ⟨hφa, hφS⟩ := hpre
  exact AutomorphicForm.PerClassReduce.per_class K L νZL D σ hgen S φa φS H hHc hH μH T ws νK νA μ hμ ν hν hφa hφS

end S_AutomorphicForm_exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure (solution)
