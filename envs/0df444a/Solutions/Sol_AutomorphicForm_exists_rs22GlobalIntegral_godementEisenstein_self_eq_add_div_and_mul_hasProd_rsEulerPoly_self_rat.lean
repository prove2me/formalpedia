-- Prove2me | solution 1 for AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/06554595-d876-54e9-881c-c8246e186dce

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat
import Theorems.Thm_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
import Theorems.Thm_NumberField_TateGlobal_exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_one_one_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_GodementSection
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rs22GlobalIntegral_godementEisenstein_eq_mul_rs22WhittakerIntegral_of_isUnitaryChar_of_re_pos_of_forall_summable_of_integrable
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
import Theorems.Thm_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure
import Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
import Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair
import Theorems.Thm_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension FLT.SpectralSide.instCompactSpaceMatrix IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_mS SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker
open scoped Classical

noncomputable section

namespace Ws46
namespace PKGQ

theorem finFactor_coe (k : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (k : AdelicGL2 (𝓞 ℚ) ℚ) = k := by
  apply Subtype.ext
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ *
    (k : AdelicGL2 (𝓞 ℚ) ℚ) = k
  have hk : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).mp k.2, map_one, map_one]
  rw [hk, map_one, inv_one, one_mul]

theorem dirichlet_ne_zero (A : ℕ) (cf : ℤ → ℝ) (B : ℝ) (hB : 1 < B) (h0 : ∀ n, 0 ≤ cf n)
    (hpos : ∃ n, -(A : ℤ) ≤ n ∧ n ≤ A ∧ 0 < cf n) :
    ∃ σS : ℝ, ∀ s : ℂ, σS < s.re →
      (∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)) ≠ 0 := by
  classical
  have hB0 : (0 : ℝ) < B := lt_trans one_pos hB
  have hBc : ((B : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB0.ne'

  set I : Finset ℤ := (Finset.Icc (-(A : ℤ)) A).filter (fun n => 0 < cf n) with hI
  have hIne : I.Nonempty := by
    obtain ⟨n, h1, h2, h3⟩ := hpos
    exact ⟨n, by rw [hI, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, h3⟩⟩
  set n₀ : ℤ := I.min' hIne with hn₀
  have hn₀I : n₀ ∈ I := Finset.min'_mem I hIne
  have hn₀mem : n₀ ∈ Finset.Icc (-(A : ℤ)) A := (Finset.mem_filter.mp hn₀I).1
  have hc₀ : 0 < cf n₀ := (Finset.mem_filter.mp hn₀I).2
  have hmin : ∀ n ∈ Finset.Icc (-(A : ℤ)) A, n < n₀ → cf n = 0 := by
    intro n hn hlt
    by_contra h
    have hnI : n ∈ I := by rw [hI, Finset.mem_filter]; exact ⟨hn, lt_of_le_of_ne (h0 n) (Ne.symm h)⟩
    exact absurd (Finset.min'_le I n hnI) (by rw [← hn₀]; exact not_le.mpr hlt)

  set T : ℝ := ∑ n ∈ (Finset.Icc (-(A : ℤ)) A).erase n₀, cf n with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => h0 n

  obtain ⟨σS, hσS0, hσS⟩ : ∃ σS : ℝ, 0 ≤ σS ∧ T * B ^ (-σS) < cf n₀ := by
    rcases eq_or_lt_of_le hT0 with hT00 | hTpos
    · exact ⟨0, le_rfl, by rw [← hT00]; simpa using hc₀⟩
    ·
      have hlim : Filter.Tendsto (fun σ : ℝ => T * B ^ (-σ)) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun σ : ℝ => B ^ (-σ)) Filter.atTop (nhds 0) := by
          have h2 := tendsto_rpow_atTop_of_base_lt_one B⁻¹
            (by linarith [inv_pos.mpr hB0]) (inv_lt_one_of_one_lt₀ hB)
          refine h2.congr' (Filter.Eventually.of_forall fun σ => ?_)
          show (B⁻¹) ^ σ = B ^ (-σ)
          rw [Real.inv_rpow hB0.le, Real.rpow_neg hB0.le]
        simpa using h1.const_mul T
      have hev := (hlim.eventually (gt_mem_nhds hc₀))
      obtain ⟨σ₁, hσ₁⟩ := (hev.and (Filter.eventually_ge_atTop 0)).exists
      exact ⟨σ₁, hσ₁.2, hσ₁.1⟩
  refine ⟨σS, fun s hs hsum => ?_⟩

  have hsplit := Finset.add_sum_erase (Finset.Icc (-(A : ℤ)) A)
    (fun n => ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)) hn₀mem
  rw [← hsplit] at hsum

  have hrest : ‖∑ n ∈ (Finset.Icc (-(A : ℤ)) A).erase n₀, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)‖
      ≤ T * B ^ (-σS) * ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ := by
    calc ‖∑ n ∈ (Finset.Icc (-(A : ℤ)) A).erase n₀, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)‖
        ≤ ∑ n ∈ (Finset.Icc (-(A : ℤ)) A).erase n₀, ‖((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ (Finset.Icc (-(A : ℤ)) A).erase n₀, cf n * (B ^ (-σS) * ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' : n ∈ Finset.Icc (-(A : ℤ)) A := Finset.mem_of_mem_erase hn
          have hne : n ≠ n₀ := Finset.ne_of_mem_erase hn
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n)]
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [hmin n hn' hlt]; simp
          · refine mul_le_mul_of_nonneg_left ?_ (h0 n)

            rw [Complex.norm_cpow_eq_rpow_re_of_pos hB0, Complex.norm_cpow_eq_rpow_re_of_pos hB0]
            have e1 : (-(n : ℂ) * s).re = -(n : ℝ) * s.re := by
              simp [Complex.mul_re]
            have e2 : (-(n₀ : ℂ) * s).re = -(n₀ : ℝ) * s.re := by
              simp [Complex.mul_re]
            rw [e1, e2, show -(n : ℝ) * s.re = (-( (n : ℝ) - (n₀ : ℝ)) * s.re) + (-(n₀ : ℝ) * s.re) by ring,
              Real.rpow_add hB0]
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hB0.le _)
            apply Real.rpow_le_rpow_of_exponent_le hB.le
            have hk : (1 : ℝ) ≤ (n : ℝ) - (n₀ : ℝ) := by
              have : n₀ + 1 ≤ n := hgt
              have := (Int.cast_le (R := ℝ)).mpr this
              push_cast at this; linarith
            have hsre : 0 ≤ s.re := le_trans hσS0 hs.le
            nlinarith
      _ = T * B ^ (-σS) * ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ := by
          rw [← Finset.sum_mul, hT]; ring

  have hmain : ‖((cf n₀ : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ = cf n₀ * ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₀.le]
  have hpow : 0 < ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hB0]; exact Real.rpow_pos_of_pos hB0 _

  have heq : ((cf n₀ : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s) =
      -∑ n ∈ (Finset.Icc (-(A : ℤ)) A).erase n₀, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s) :=
    eq_neg_of_add_eq_zero_left hsum
  have := congrArg norm heq
  rw [norm_neg, hmain] at this
  have hlt : T * B ^ (-σS) * ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ < cf n₀ * ‖((B : ℝ) : ℂ) ^ (-(n₀ : ℂ) * s)‖ :=
    mul_lt_mul_of_pos_right hσS hpow
  linarith [hrest]

end Ws46.PKGQ

section PsiNormSec
open NumberField NumberField.StandardAddChar IsDedekindDomain
namespace Ws46
namespace PsiNorm

theorem norm_exp_neg_two_pi_I_mul_ofReal (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [show -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ‖psiPadicFun x‖ = 1 := by
  obtain ⟨a, k, ha⟩ := exists_pPow_approx x
  rw [psiPadicFun_eq ha, show ((a : ℂ) / (p : ℂ) ^ k) = (((a : ℝ) / (p : ℝ) ^ k : ℝ) : ℂ) by push_cast; ring]
  exact norm_exp_neg_two_pi_I_mul_ofReal _

theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  rw [psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun _

theorem norm_psiFin (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : ‖psiFin x‖ = 1 := by
  rw [psiFin_apply, finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_psiV_finite x).toFinset)
    (by intro v hv; simpa using hv), norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiV v _

theorem norm_psiArch (x : InfiniteAdeleRing ℚ) : ‖psiArch x‖ = 1 := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [psiArchPlace_apply, show (2 * Real.pi * Complex.I) *
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (x v) : ℝ) : ℂ) =
      ((2 * Real.pi * (InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (x v) : ℝ) : ℝ) : ℂ) *
        Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_psiQ (x : AdeleRing (𝓞 ℚ) ℚ) : ‖psiQ x‖ = 1 := by
  rw [psiQ_apply, norm_mul, norm_psiArch, norm_psiFin, mul_one]

end Ws46.PsiNorm
end PsiNormSec

open Ws46.PKGQ in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Θ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (σ₀ x : ℝ), x < 0 ∧
    ∃ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
      (n : ℕ) (coef : Fin n → ℂ) (φs φs' : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (Φs : Fin n → (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
      (Zr H : ℂ → ℂ) (c₁ c₀ : ℂ),
      ν₀.IsHaarMeasure ∧
      (∀ i : Fin n, Φs i ∈ schwartzBruhat2 ℚ) ∧
      Differentiable ℂ Zr ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∑ i : Fin n, coef i * rs22GlobalIntegral ℚ D (φs i) (φs' i)
            (godementEisenstein ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) (Φs i) (s - 1 / 2))) =
          Zr s + c₁ / (s - 1) + c₀ / s) ∧
      (∀ σ : ℝ, x < σ → AnalyticAt ℂ H (σ : ℂ)) ∧
      (c₀ = 0 ∨ H 0 = 0) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
          ((Zr s + c₁ / (s - 1) + c₀ / s) * H s)) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ
  haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hHaar, -⟩ := LanglandsTunnell.Converse.isHaarMeasure_and_isMulRightInvariant_archMeasure
  obtain ⟨μf, hμf, -, hsplit⟩ := LanglandsTunnell.Converse.exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
  obtain ⟨μNArch, μNFin, hNA, hNF, hNsplit⟩ :=
    LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
  haveI := hμf; haveI := hNA; haveI := hNF; haveI := hHaar

  obtain ⟨ν₀, -, hν₀, -, -, -⟩ :=
    NumberField.TateGlobal.exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top ℚ
  haveI := hν₀
  haveI hAH : (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).IsAddHaarMeasure :=
    NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  have hbox0 : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ) ≠ 0 :=
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
  have hboxT : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ) ≠ ⊤ :=
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne
  set μ₁ : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ))⁻¹ • NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ₁def
  haveI hμ₁ : μ₁.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hboxT) (ENNReal.inv_ne_top.mpr hbox0)
  have hμ₁box : μ₁ (adelicBox ℚ) = 1 := by
    rw [hμ₁def, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hbox0 hboxT]
  have hψ : IsGlobalAddChar ℚ NumberField.StandardAddChar.psiQ := NumberField.StandardAddChar.isGlobalAddChar_psiQ
  have hprin : IsPrincipalTrivial (R := 𝓞 ℚ) (K := ℚ) (moduleChar ℚ) := by
    intro q
    apply Units.ext
    rw [val_moduleChar_apply, Units.val_one]
    unfold NumberField.TateGlobal.ideleNorm
    have := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ q
    erw [this]
    simp

  obtain ⟨S, φ, φ', WA, WA', FA, Wf, Wf', Ff, Φ, ω, P, x₀, xH, Hinf, ϖ, hπ, lam, om, lam', om', κ, D, e₁, e₂,
    cS, uS, tS, hφc, hφ'c, hφd, hφ'd, hφl, hφ'l, hω, hφz, hφ'z, hφ'cusp, hφsum, hφ'sum, hΦ, he₁, he, hcS, hDm, hDμ, hDs, hD, hDS, hW, hW', hΦsplit, hFA, hWAm, hWA'm, hPm, hWfm, hWf'm, hFfm, hN, hK, hT, hP0, hPne, hPint, hxH, hHinf, hHinf0, hHinf1, hϖ, hbd, hfinv, hNψ, hWK, hFK, hTfin, hresc, hsupp, hC6⟩ :=
    AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ

  obtain ⟨hwinv, σd, hconv⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat
    c u d₁ d₂ T S φ φ' WA WA' FA Wf Wf' Ff Φ P x₀ D e₁ e₂ cS uS tS
    hφc hφ'c hφd hφ'd hφl hφ'l hΦ he₁ he hcS hDm hDμ hDs hDS hW hW' hΦsplit hFA hT hP0 hPint hWfm hWf'm hFfm
    ⟨hWAm, hWA'm, hPm, hN, hK⟩ ϖ hπ lam om lam' om' κ ⟨hϖ, hbd, hfinv, hNψ, hWK, hFK, hTfin⟩ hsupp

  obtain ⟨R, R', X, w, c₁, c₀, hRd, -, hRc, -, hRb, -, hXc, hw, hX, hE, -, -⟩ :=
    LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_one_one_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
      ℚ ν₀ μ₁ hμ₁box NumberField.StandardAddChar.psiQ hψ (moduleChar_pos ℚ) hprin Φ hΦ

  obtain ⟨Cunf, hCunf, hunf⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rs22GlobalIntegral_godementEisenstein_eq_mul_rs22WhittakerIntegral_of_isUnitaryChar_of_re_pos_of_forall_summable_of_integrable
      ℚ ν₀ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
      NumberField.StandardAddChar.psiQ hψ Ws46.PsiNorm.norm_psiQ e₁ e₂ he₁ he

  obtain ⟨C', hC', hG5⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile hHaar μNArch
  obtain ⟨M, hMan, hMpos, hMint, hMeq⟩ := hG5 WA WA' P x₀ hWAm hWA'm hPm hN hK hT hP0 hPne hPint

  obtain ⟨A, cf, B, hB, hcf0, hcfpos, hΨeq⟩ := hC6 μf μNFin
  obtain ⟨σS, hσS⟩ := dirichlet_ne_zero A cf B hB hcf0 hcfpos

  obtain ⟨σ3, hC3⟩ :=
    LanglandsTunnell.RankinSelberg.exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
      μf μNFin S ϖ hπ hϖ lam om lam' om' κ hbd
      (fun g => Wf (finFactor g)) (fun g => Wf' (finFactor g) * Ff (finFactor g))
      (fun n g => by simp only [finFactor_coe]; exact hfinv n g) hNψ hWK hFK hTfin

  obtain ⟨hintR, hdiffR, -⟩ :=
    LanglandsTunnell.RankinSelberg.integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
      ℚ cS uS hcS tS D hDm hDμ hDS φ φ' hφc hφ'c hφd hφ'd R hRd hRc hRb
  have hXb : IsUniformlySiegelBounded ℚ (fun (_ : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) => X g) := by
    intro σ₁ σ₂ c' u' t hc'
    refine ⟨1, 0, fun s _ _ g _ => ?_⟩
    show ‖X (g * t)‖ ≤ _
    rw [hX, AutomorphicForm.norm_cpowChar_apply, hw, Real.rpow_zero, pow_zero, mul_one]
  obtain ⟨hintX, -, -⟩ :=
    LanglandsTunnell.RankinSelberg.integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
      ℚ cS uS hcS tS D hDm hDμ hDS φ φ' hφc hφ'c hφd hφ'd (fun (_ : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) => X g)
      (fun _ => differentiable_const _) (hXc.comp continuous_snd) hXb

  have hZ : ∀ s : ℂ, 1 < s.re →
      rs22GlobalIntegral ℚ D φ φ' (godementEisenstein ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)) =
        rs22GlobalIntegral ℚ D φ φ' (R (s - 1 / 2)) + c₁ * rs22GlobalIntegral ℚ D φ φ' X / (s - 1) +
          c₀ * rs22GlobalIntegral ℚ D φ φ' X / s := by
    intro s hs1
    have hs' : (1 / 2 : ℝ) < (s - 1 / 2).re := by
      have : (s - 1 / 2).re = s.re - 1 / 2 := by simp
      rw [this]; linarith
    have hEfun : godementEisenstein ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) =
        R (s - 1 / 2) + (c₁ / (s - 1) + c₀ / s) • X := by
      funext g
      rw [hE _ hs' g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      rw [show s - 1 / 2 - 1 / 2 = s - 1 by ring, show s - 1 / 2 + 1 / 2 = s by ring]
    have hI1 : IntegrableOn (fun g => φ g * φ' g * R (s - 1 / 2) g) D (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
      hintR (s - 1 / 2)
    have hI2 : IntegrableOn (fun g => φ g * φ' g * ((c₁ / (s - 1) + c₀ / s) • X) g) D
        (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
      have h0 : IntegrableOn (fun g => (c₁ / (s - 1) + c₀ / s) * (φ g * φ' g * X g)) D (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
        (hintX 0).const_mul (c₁ / (s - 1) + c₀ / s)
      refine IntegrableOn.congr_fun h0 (fun g _ => ?_) hDm
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hEfun, rs22GlobalIntegral_add_right _ _ _ _ _ _ hI1 hI2, rs22GlobalIntegral_smul_right]
    ring

  refine ⟨S, max (max σd σ3) (max (max x₀ 2) σS), xH, hxH, ν₀, D, 1, fun _ => 1, fun _ => φ, fun _ => φ', fun _ => Φ,
    fun s => rs22GlobalIntegral ℚ D φ φ' (R (s - 1 / 2)),
    fun s => Hinf s * ((Cunf : ℂ) * (C' : ℂ) *
      ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2)))⁻¹,
    c₁ * rs22GlobalIntegral ℚ D φ φ' X, c₀ * rs22GlobalIntegral ℚ D φ φ' X,
    hν₀, fun _ => hΦ, ?hZr, ?hpolar, ?hH, ?hH0, ?hprod⟩
  · exact hdiffR.comp (differentiable_id.sub_const (1 / 2 : ℂ))
  · intro s hs
    have hs1 : (1 : ℝ) < s.re := by
      have := le_trans (le_trans (by norm_num : (1:ℝ) ≤ 2) (le_max_right x₀ 2)) (le_trans (le_max_left _ σS) (le_max_right (max σd σ3) _))
      linarith
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul]
    rw [hZ s hs1]
  · intro σ' hσ'
    have hB0 : (0 : ℝ) < B := lt_trans one_pos hB
    have hBc : ((B : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB0.ne'
    have dD : Differentiable ℂ (fun s : ℂ =>
        ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) := by
      refine Differentiable.fun_sum fun n _ => (differentiable_const _).mul ?_
      have : (fun s : ℂ => ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) =
          fun s => Complex.exp (Complex.log ((B : ℝ) : ℂ) * (-(n : ℂ) * (s + 1 / 2))) := by
        funext s; rw [Complex.cpow_def_of_ne_zero hBc]
      rw [this]
      exact Complex.differentiable_exp.comp ((differentiable_const _).mul
        ((differentiable_const _).mul (differentiable_id.add_const _)))
    have Dne : (∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * ((σ' : ℂ) + 1 / 2))) ≠ 0 := by
      have hreal : (∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * ((σ' : ℂ) + 1 / 2))) =
          ((∑ n ∈ Finset.Icc (-(A : ℤ)) A, cf n * B ^ (-(n : ℝ) * (σ' + 1 / 2)) : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [show (-(n : ℂ) * ((σ' : ℂ) + 1 / 2)) = ((-(n : ℝ) * (σ' + 1 / 2) : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hB0.le]
      rw [hreal]
      obtain ⟨n₀, hn₀a, hn₀b, hn₀⟩ := hcfpos
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Finset.sum_pos'
        (fun n _ => mul_nonneg (hcf0 n) (Real.rpow_nonneg hB0.le _))
        ⟨n₀, Finset.mem_Icc.mpr ⟨hn₀a, hn₀b⟩, mul_pos hn₀ (Real.rpow_pos_of_pos hB0 _)⟩))
    have hCne : (Cunf : ℂ) * (C' : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hCunf.ne') (Complex.ofReal_ne_zero.mpr hC'.ne')
    have hA2 : AnalyticAt ℂ (fun s : ℂ => (Cunf : ℂ) * (C' : ℂ) *
        ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) (σ' : ℂ) :=
      (dD.const_mul ((Cunf : ℂ) * (C' : ℂ))).analyticAt _
    exact (hHinf σ' hσ').mul (hA2.inv (mul_ne_zero hCne Dne))
  · right
    simp [hHinf0]
  ·
    intro s hs
    have hA1 : max σd σ3 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hA2' : max (max x₀ 2) σS < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hσd : σd < s.re := lt_of_le_of_lt (le_max_left _ _) hA1
    have hσ3 : σ3 < s.re := lt_of_le_of_lt (le_max_right _ _) hA1
    have hx₀ : x₀ < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hA2'
    have h2re : (2 : ℝ) < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hA2'
    have hσS' : σS < s.re := lt_of_le_of_lt (le_max_right _ _) hA2'
    have hs0 : 0 < s.re := by linarith
    have hs1 : 1 < s.re := by linarith
    have hsmax : max x₀ 0 < s.re := max_lt hx₀ hs0
    obtain ⟨hm, hsum, hfold, hunfI, hintC2, hintC3, hintG5⟩ := hconv s hσd ν₀ μf μNArch μNFin

    have hsumAll : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Summable fun ξ : ℚ =>
        ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
          (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * g)‖ :=
      AutomorphicForm.summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re ℚ ν₀ 1 1
        (fun _ => rfl) (fun _ => rfl) (fun _ => by simp) (fun _ => by simp)
        (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
        (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
        Φ hΦ (s - 1 / 2) (by simp; linarith)
    have h1 := hunf 1 1 ω ω⁻¹ (fun _ => rfl) (fun _ => rfl) (fun _ => by simp) (fun _ => by simp)
      (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
      (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
      (by ext x; simp) Φ hΦ φ φ' hφc hφ'c hφl hφ'l hφz hφ'z hφsum hφ'sum hφ'cusp
      (s - 1 / 2) (by simp; linarith) D hDs hD hsum hsumAll hfold hunfI

    have h2 := LanglandsTunnell.RankinSelberg.rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
      μf μNArch μNFin hsplit hNsplit (s - 1 / 2) _ _ WA WA' FA Wf Wf' Ff Φ hW hW' hΦsplit hm hwinv hintC2
    rw [show s - 1 / 2 + 1 = s + 1 / 2 by ring] at h2
    have hFAfun : FA = fun g : GL (Fin 2) ℝ => Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)) := funext hFA
    rw [hFAfun] at h2
    simp only [] at h2

    have h5 := hMeq s hs0 hintG5

    have hs3' : σ3 < (s + 1 / 2).re := by simp; linarith
    obtain ⟨Prod, hProd, h3⟩ := hC3 (s + 1 / 2) hs3' hintC3
    simp only [finFactor_coe] at h3

    have h6 := hΨeq (s + 1 / 2)

    have hHM : Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * M s) = 1 := by
      rw [hMint s hx₀]; exact hHinf1 s hsmax
    have hD0 : (∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) ≠ 0 :=
      hσS (s + 1 / 2) (by simp; linarith)
    have hCD : (Cunf : ℂ) * (C' : ℂ) *
        (∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hCunf.ne') (Complex.ofReal_ne_zero.mpr hC'.ne')) hD0

    have hfacfun : (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
        ((rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹ (Θ.a v.1) (Θ.b v.1) 0).eval
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) =
        fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((rsEulerPoly (lam v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))
              (lam' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((3 / 2 : ℂ) - (s + 1 / 2))))⁻¹ := by
      funext v
      have hN : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := by
        have : Ideal.absNorm v.1.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
        exact_mod_cast this
      rw [← hresc v.1 v.2 (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)),
        show (3 / 2 : ℂ) - (s + 1 / 2) = 1 + (-s) by ring, Complex.cpow_add _ _ hN, Complex.cpow_one]

    have hval : (rs22GlobalIntegral ℚ D φ φ' (R (s - 1 / 2)) + c₁ * rs22GlobalIntegral ℚ D φ φ' X / (s - 1) +
          c₀ * rs22GlobalIntegral ℚ D φ φ' X / s) *
        (Hinf s * ((Cunf : ℂ) * (C' : ℂ) *
          ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2)))⁻¹) = Prod := by
      rw [← hZ s hs1, h1, h2, h5, h3, h6]
      calc (Cunf : ℂ) * ((C' : ℂ) * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s) * M s *
            ((∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) * Prod)) *
          (Hinf s * ((Cunf : ℂ) * (C' : ℂ) *
            ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2)))⁻¹)
          = Prod * (Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * M s)) *
            (((Cunf : ℂ) * (C' : ℂ) *
              ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))) *
             ((Cunf : ℂ) * (C' : ℂ) *
              ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2)))⁻¹) := by ring
        _ = Prod := by rw [hHM, mul_inv_cancel₀ hCD]; ring
    show HasProd _ ((rs22GlobalIntegral ℚ D φ φ' (R (s - 1 / 2)) + c₁ * rs22GlobalIntegral ℚ D φ φ' X / (s - 1) +
          c₀ * rs22GlobalIntegral ℚ D φ φ' X / s) *
        (Hinf s * ((Cunf : ℂ) * (C' : ℂ) *
          ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * (s + 1 / 2)))⁻¹))
    rw [hval, hfacfun]
    exact hProd

end

end S_AutomorphicForm_exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat (solution)
