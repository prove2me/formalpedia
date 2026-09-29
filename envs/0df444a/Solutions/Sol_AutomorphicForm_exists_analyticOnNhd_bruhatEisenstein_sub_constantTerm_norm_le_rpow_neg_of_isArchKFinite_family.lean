-- Prove2me | solution 1 for AutomorphicForm.exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/681d8ab1-56a6-5167-9793-fe8bd7dab6cd

import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary
import Theorems.Thm_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Compactness.LocallyCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
p2m_open "AutomorphicForm~isIdeleClassChar_one IsDedekindDomain Filter Topology"
open scoped NNReal

noncomputable section

namespace B2Proof

section LocCompact

variable (F : Type) [Field F] [NumberField F]

scoped instance weaklyLocallyCompactSpace_finiteAdeleRing : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) where
  exists_compact_mem_nhds x := by
    refine ⟨(fun y => x + y) '' AdelicLevel.integralFiniteAdeles (𝓞 F) F, ?_, ?_⟩
    · exact (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 F) F).image (continuous_const.add continuous_id)
    · rw [← map_add_left_nhds_zero]
      exact Filter.image_mem_map ((AdelicLevel.isOpen_integralFiniteAdeles (𝓞 F) F).mem_nhds
        AdelicLevel.zero_mem_integralFiniteAdeles)

scoped instance weaklyLocallyCompactSpace_adeleRing : WeaklyLocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (WeaklyLocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

scoped instance weaklyLocallyCompactSpace_matrix :
    WeaklyLocallyCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (WeaklyLocallyCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))

scoped instance weaklyLocallyCompactSpace_adelicGL2 : WeaklyLocallyCompactSpace (AdelicGL2 (𝓞 F) F) :=
  (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).weaklyLocallyCompactSpace

end LocCompact

section Helpers

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem isUnitaryChar_one : IsUnitaryChar R K (1 : (AdeleRing R K)ˣ →* ℂˣ) := by
  intro x; simp

theorem isIdeleClassChar_one : IsIdeleClassChar R K (1 : (AdeleRing R K)ˣ →* ℂˣ) := by
  intro x; simp

end Helpers

theorem closedBall_subset_re_pos {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    Metric.closedBall s₀ (s₀.re / 2) ⊆ {s : ℂ | 0 < s.re} := by
  intro z hz
  rw [Metric.mem_closedBall] at hz
  simp only [Set.mem_setOf_eq]
  have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
  rw [dist_eq_norm] at hz
  have h2 : |z.re - s₀.re| ≤ s₀.re / 2 := by simpa [Complex.sub_re] using h1.trans hz
  have := (abs_le.mp h2).1
  linarith

end B2Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family.B2Proof"

namespace B2Proof

variable (F : Type) [Field F] [NumberField F]

theorem main :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ Wnc : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Wnc s h) {s : ℂ | 0 < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Wnc s h = E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            unipotentGL2 (E s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Wnc p.1 p.2)
        ({s : ℂ | 0 < s.re} ×ˢ Set.univ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → C ⊆ {s : ℂ | 0 < s.re} → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            ‖Wnc s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) := by
  intro α hα φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  classical

  have hψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F
  obtain ⟨𝒲, h1, h2, h3, h4, h5⟩ :=
    AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family
      F hα (NumberField.StandardAddChar.stdAddChar F) hψ φ hφ hφK hφf hφjc hφhol
  let Wnc : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h => ∑' ξ : {ξ : F // ξ ≠ 0}, 𝒲 ξ s h
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re

  have hWan : ∀ h, AnalyticOnNhd ℂ (fun s => Wnc s h) {s : ℂ | 0 < s.re} := by
    intro h
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s₀ hs₀
    have hr : 0 < s₀.re / 2 := by simp only [Set.mem_setOf_eq] at hs₀; linarith
    have hsub := closedBall_subset_re_pos hs₀
    obtain ⟨u, hu, hle⟩ := h4 (Metric.closedBall s₀ (s₀.re / 2)) {h} (isCompact_closedBall _ _) hsub
      isCompact_singleton
    have hd : DifferentiableOn ℂ (fun s => Wnc s h) (Metric.ball s₀ (s₀.re / 2)) :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun ξ => ((h1 ξ h).differentiableOn).mono (Metric.ball_subset_closedBall.trans hsub))
        Metric.isOpen_ball (fun ξ w hw => hle ξ w (Metric.ball_subset_closedBall hw) h rfl)
    exact (hd.differentiableAt (Metric.ball_mem_nhds _ hr)).differentiableWithinAt

  have hWco : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Wnc p.1 p.2) ({s : ℂ | 0 < s.re} ×ˢ Set.univ) := by
    rw [(hU.prod isOpen_univ).continuousOn_iff]
    rintro ⟨s₀, h₀⟩ ⟨hs₀, -⟩
    obtain ⟨Ω, hΩc, hΩn⟩ := exists_compact_mem_nhds h₀
    have hr : 0 < s₀.re / 2 := by simp only [Set.mem_setOf_eq] at hs₀; linarith
    have hsub := closedBall_subset_re_pos hs₀
    obtain ⟨u, hu, hle⟩ := h4 (Metric.closedBall s₀ (s₀.re / 2)) Ω (isCompact_closedBall _ _) hsub hΩc
    have hc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Wnc p.1 p.2) (Metric.closedBall s₀ (s₀.re / 2) ×ˢ Ω) :=
      continuousOn_tsum (fun ξ => (h3 ξ).mono (Set.prod_mono hsub (Set.subset_univ _))) hu
        (fun ξ p hp => hle ξ p.1 hp.1 p.2 hp.2)
    exact hc.continuousAt (prod_mem_nhds (Metric.closedBall_mem_nhds _ hr) hΩn)

  have hagree1 : ∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
      Wnc s h = (φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)) -
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
          (fun h' => φ s h' + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h')) h := by
    intro s h hs
    have hF := AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary F hα 1 1
      isUnitaryChar_one isUnitaryChar_one (NumberField.StandardAddChar.stdAddChar F) hψ φ hφ hφK hφf
      (fun s => hφjc.comp (Continuous.prodMk_right s)) h s hs
    beta_reduce at hF
    have hW : Wnc s h = ∑' ξ : {ξ : F // ξ ≠ 0}, whittakerCoefficient F (productionPins F)
        (NumberField.StandardAddChar.stdAddChar F)
        (fun h' => φ s h' + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h'))
        (ξ : F) h := by
      show (∑' ξ : {ξ : F // ξ ≠ 0}, 𝒲 ξ s h) = _
      exact tsum_congr (fun ξ => h2 ξ s h hs)
    rw [hW]
    rw [eq_sub_iff_add_eq']
    exact hF.symm

  set Efun : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
    φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h) with hEfun
  set CT : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (Efun s) h with hCT
  have hagree1' : ∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re → Wnc s h = Efun s h - CT s h := by
    intro s h hs; exact hagree1 s h hs

  have hEd : ∀ h, DifferentiableOn ℂ (fun s => Efun s h) {s : ℂ | 1 / 2 < s.re} := by
    intro h
    exact AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family F hα 1 1
      isUnitaryChar_one isUnitaryChar_one φ hφ hφjc hφhol h

  have hCTd : ∀ h, DifferentiableOn ℂ (fun s => CT s h) {s : ℂ | 1 / 2 < s.re} := by
    intro h
    obtain ⟨a, Mreg, ha, hMan, hMeq, -, -⟩ :=
      AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
        F hα φ hφ hφK hφf hφjc hφhol
    have hO : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hform : ∀ s ∈ {s : ℂ | 1 / 2 < s.re}, CT s h = φ s h + (s - 1 / 2)⁻¹ * Mreg s h := by
      intro s hs
      simp only [Set.mem_setOf_eq] at hs
      have hne : (s - 1 / 2 : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hct := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hα 1 1
        isUnitaryChar_one isUnitaryChar_one s hs (φ s) (hφ s) (hφjc.comp (Continuous.prodMk_right s)) h
      simp only at hct
      show constantTerm _ unipotentGL2 (Efun s) h = _
      rw [hEfun]
      rw [hct, hMeq s h hs]
      congr 1
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    refine DifferentiableOn.congr ?_ hform
    refine ((hφhol h).differentiableOn).add (DifferentiableOn.mul ?_ ?_)
    · exact (differentiableOn_id.sub (differentiableOn_const _)).inv (fun s hs h0 => by
        simp only [Set.mem_setOf_eq] at hs
        have := congrArg Complex.re h0; simp at this; linarith)
    · exact ((hMan h).mono (fun s hs => by simp only [Set.mem_setOf_eq] at hs ⊢; linarith)).differentiableOn

  have hagree : ∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re → Wnc s h = Efun s h - CT s h := by
    intro s h hs
    have hO : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
    have hf₁ : AnalyticOnNhd ℂ (fun s => Wnc s h) {s : ℂ | 1 / 2 < s.re} :=
      (hWan h).mono (fun s hs => by simp only [Set.mem_setOf_eq] at hs ⊢; linarith)
    have hf₂ : AnalyticOnNhd ℂ (fun s => Efun s h - CT s h) {s : ℂ | 1 / 2 < s.re} :=
      ((hEd h).sub (hCTd h)).analyticOnNhd hO
    have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
    have hev : (fun s => Wnc s h) =ᶠ[𝓝 (2 : ℂ)] (fun s => Efun s h - CT s h) := by
      have hO1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
      filter_upwards [hO1.mem_nhds h2] with s hs'
      exact hagree1' s h hs'
    exact hf₁.eqOn_of_preconnected_of_eventuallyEq hf₂ hpre h2mem hev hs

  refine ⟨Wnc, hWan, ?_, hWco, ?_⟩
  · intro s h hs
    exact hagree s h hs
  · intro C Ω c' N hC hCU hΩ hc'
    obtain ⟨M, hM⟩ := h5 C Ω c' N hC hCU hΩ hc'
    refine ⟨M, fun s hs b ω hω hb => ?_⟩
    obtain ⟨hsum, hle⟩ := hM s hs b ω hω hb
    calc ‖Wnc s ((b : AdelicGL2 (𝓞 F) F) * ω)‖
        = ‖∑' ξ : {ξ : F // ξ ≠ 0}, 𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ := rfl
      _ ≤ ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ := norm_tsum_le_tsum_norm hsum
      _ ≤ M * _ := hle

end B2Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family.B2Proof"

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ Wnc : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Wnc s h) {s : ℂ | 0 < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Wnc s h = E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            unipotentGL2 (E s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Wnc p.1 p.2)
        ({s : ℂ | 0 < s.re} ×ˢ Set.univ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → C ⊆ {s : ℂ | 0 < s.re} → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            ‖Wnc s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) :=
  B2Proof.main F

end
end S_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family (solution)
