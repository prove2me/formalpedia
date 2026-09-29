-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/af2f495e-5313-59a5-81cc-6f25fb5f81e4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_schemeNsmul_pullback_translation_iso
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Theorems.Thm_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul
import Theorems.Thm_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_AlgPoints_exists_nsmul_eq_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul
import Theorems.Thm_AlgebraicGeometry_Polarisation_mapPt_negMor_mul
import Theorems.Thm_AlgebraicGeometry_Polarisation_schemeNsmul_comp_negMor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm CategoryTheory.MonoidalCategory"

open scoped commutatorElement

noncomputable section

namespace TgTpow

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative)

abbrev H (M₁ M₂ : A.Modules) : Subgroup (thetaGroup f L hc M₁ × thetaGroup f L hc M₂) :=
  MonoidHom.eqLocus
    ((thetaGroup.pt f L hc M₁).comp (MonoidHom.fst (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))
    ((thetaGroup.pt f L hc M₂).comp (MonoidHom.snd (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))

def Over {G : Type} [Group G] (M : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) (φ : C → k) : Prop :=
  ∃ α : G →* thetaGroup f L hc M, (∀ g, thetaGroup.pt f L hc M (α g) = π g) ∧
    (∀ g c, S g c → thetaGroup.IsScalarElt f L hc M (α g) (φ c))

def pairHom {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    (α : G →* thetaGroup f L hc M₁) (β : G →* thetaGroup f L hc M₂)
    (hα : ∀ g, thetaGroup.pt f L hc M₁ (α g) = π g) (hβ : ∀ g, thetaGroup.pt f L hc M₂ (β g) = π g) :
    G →* H f L hc M₁ M₂ :=
  (α.prod β).codRestrict _ (fun g => show thetaGroup.pt f L hc M₁ (α g) = thetaGroup.pt f L hc M₂ (β g) by
    rw [hα, hβ])

theorem pairHom_fst {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    (α : G →* thetaGroup f L hc M₁) (β : G →* thetaGroup f L hc M₂)
    (hα : ∀ g, thetaGroup.pt f L hc M₁ (α g) = π g) (hβ : ∀ g, thetaGroup.pt f L hc M₂ (β g) = π g) (g : G) :
    (pairHom f L hc M₁ M₂ π α β hα hβ g).1.1 = α g := rfl

theorem pairHom_snd {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    (α : G →* thetaGroup f L hc M₁) (β : G →* thetaGroup f L hc M₂)
    (hα : ∀ g, thetaGroup.pt f L hc M₁ (α g) = π g) (hβ : ∀ g, thetaGroup.pt f L hc M₂ (β g) = π g) (g : G) :
    (pairHom f L hc M₁ M₂ π α β hα hβ g).1.2 = β g := rfl

theorem tensor_of {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) (φ₁ φ₂ : C → k)
    (h₁ : Over f L hc M₁ π S φ₁) (h₂ : Over f L hc M₂ π S φ₂) :
    Over f L hc (M₁ ⊗ M₂) π S (fun c => φ₁ c * φ₂ c) := by
  obtain ⟨α, hα, hαs⟩ := h₁
  obtain ⟨β, hβ, hβs⟩ := h₂
  obtain ⟨τ, τpt, τsc⟩ := thetaGroup.exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul k f L hc M₁ M₂
  refine ⟨τ.comp (pairHom f L hc M₁ M₂ π α β hα hβ), fun g => ?_, fun g c hg => ?_⟩
  · rw [MonoidHom.comp_apply, τpt, pairHom_fst, hα]
  · rw [MonoidHom.comp_apply]
    exact τsc _ _ _ (hαs g c hg) (hβs g c hg)

theorem transport_of {G : Type} [Group G] (M₁ M₂ : A.Modules) (ι : M₁ ≅ M₂)
    (π : G →* Multiplicative (L.AlgPoints hc k)) {C : Type} (S : G → C → Prop) (φ : C → k)
    (h₁ : Over f L hc M₁ π S φ) : Over f L hc M₂ π S φ := by
  obtain ⟨α, hα, hαs⟩ := h₁
  obtain ⟨τ, τpt, τsc⟩ := thetaGroup.exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso k f L hc M₁ M₂ ι
  refine ⟨τ.toMonoidHom.comp α, fun g => ?_, fun g c hg => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, τpt, hα]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (τsc _ _).1 (hαs g c hg)

theorem over_congr {G : Type} [Group G] (M : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) {φ ψ : C → k} (e : ∀ c, φ c = ψ c) (h : Over f L hc M π S φ) :
    Over f L hc M π S ψ := by
  obtain ⟨α, hα, hαs⟩ := h
  exact ⟨α, hα, fun g c hg => (e c) ▸ hαs g c hg⟩

theorem tpow_succ_of {G : Type} [Group G] (M : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) (φ : C → k) (h : Over f L hc M π S φ) : ∀ n : ℕ,
    Over f L hc (Scheme.Modules.tpow M (n + 1)) π S (fun c => φ c ^ (n + 1))
  | 0 => by
      have h' : Over f L hc (𝟙_ _ ⊗ M) π S φ := transport_of f L hc M (𝟙_ _ ⊗ M) (λ_ M).symm π S φ h
      exact over_congr f L hc _ π S (fun c => (pow_one (φ c)).symm) h'
  | n + 1 => by
      have h' := tensor_of f L hc (Scheme.Modules.tpow M (n + 1)) M π S (fun c => φ c ^ (n + 1)) φ
        (tpow_succ_of M π S φ h n) h
      exact over_congr f L hc _ π S (fun c => (pow_succ (φ c) (n + 1)).symm) h'

theorem tpow_hom (M : A.Modules) (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : thetaGroup f L hc M →* thetaGroup f L hc (Scheme.Modules.tpow M n),
      (∀ g, thetaGroup.pt f L hc (Scheme.Modules.tpow M n) (ρ g) = thetaGroup.pt f L hc M g) ∧
      (∀ g c, thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (Scheme.Modules.tpow M n) (ρ g) (c ^ n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact tpow_succ_of f L hc M (thetaGroup.pt f L hc M) (fun g c => thetaGroup.IsScalarElt f L hc M g c) (fun c => c)
    ⟨MonoidHom.id _, fun _ => rfl, fun _ _ hg => hg⟩ m

theorem tpow_tensor_hom (𝓜 𝓝 : A.Modules) (a b : ℕ) (hab : 1 ≤ a + b) :
    ∃ ρ : H f L hc 𝓜 𝓝 →* thetaGroup f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b),
      (∀ p, thetaGroup.pt f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b) (ρ p) =
        thetaGroup.pt f L hc 𝓜 p.1.1) ∧
      (∀ p (c₁ c₂ : k), thetaGroup.IsScalarElt f L hc 𝓜 p.1.1 c₁ → thetaGroup.IsScalarElt f L hc 𝓝 p.1.2 c₂ →
        thetaGroup.IsScalarElt f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b) (ρ p) (c₁ ^ a * c₂ ^ b)) := by
  let π : H f L hc 𝓜 𝓝 →* Multiplicative (L.AlgPoints hc k) :=
    (thetaGroup.pt f L hc 𝓜).comp ((MonoidHom.fst _ _).comp (H f L hc 𝓜 𝓝).subtype)
  let S : H f L hc 𝓜 𝓝 → k × k → Prop := fun p c =>
    thetaGroup.IsScalarElt f L hc 𝓜 p.1.1 c.1 ∧ thetaGroup.IsScalarElt f L hc 𝓝 p.1.2 c.2
  have h𝓜 : Over f L hc 𝓜 π S (fun c => c.1) :=
    ⟨(MonoidHom.fst _ _).comp (H f L hc 𝓜 𝓝).subtype, fun _ => rfl, fun _ _ hg => hg.1⟩
  have h𝓝 : Over f L hc 𝓝 π S (fun c => c.2) :=
    ⟨(MonoidHom.snd _ _).comp (H f L hc 𝓜 𝓝).subtype, fun p => p.2.symm, fun _ _ hg => hg.2⟩

  suffices hO : Over f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b) π S (fun c => c.1 ^ a * c.2 ^ b) by
    obtain ⟨ρ, hρ, hρs⟩ := hO
    exact ⟨ρ, hρ, fun p c₁ c₂ h₁ h₂ => hρs p (c₁, c₂) ⟨h₁, h₂⟩⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  ·
    subst ha
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hB := tpow_succ_of f L hc 𝓝 π S (fun c => c.2) h𝓝 b'
    have hT := transport_of f L hc _ (𝟙_ _ ⊗ Scheme.Modules.tpow 𝓝 (b' + 1)) (λ_ _).symm π S _ hB
    exact over_congr f L hc _ π S (fun c => by simp only [pow_zero, one_mul]) hT
  rcases Nat.eq_zero_or_pos b with hb | hb
  ·
    subst hb
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hA := tpow_succ_of f L hc 𝓜 π S (fun c => c.1) h𝓜 a'
    have hT := transport_of f L hc _ (Scheme.Modules.tpow 𝓜 (a' + 1) ⊗ 𝟙_ _) (ρ_ _).symm π S _ hA
    exact over_congr f L hc _ π S (fun c => by simp only [pow_zero, mul_one]) hT
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact tensor_of f L hc _ _ π S _ _ (tpow_succ_of f L hc 𝓜 π S (fun c => c.1) h𝓜 a')
      (tpow_succ_of f L hc 𝓝 π S (fun c => c.2) h𝓝 b')

end TgTpow

namespace K79COMM

variable {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : schemeHomOverComp ψ hψ (L.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    change L.mul t' _ _ = L.one t'
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural t t' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h

theorem mapPt_schemeNsmul (m : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) P = L.nsmul t m P := by
  have h := L.nsmul_natural f t P.1 P.2 m (RelativeGroupLaw.idPoint (f := f))
  have h2 : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (Category.comp_id _)
  rw [h2] at h
  rw [← h]
  rfl

theorem mapPt_negMor {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) P = L.inv t P := by
  have h := inv_natural L f t P.1 P.2 (Polarisation.idPt f)
  have h2 : schemeHomOverComp P.1 P.2 (Polarisation.idPt f) = P := Subtype.ext (Category.comp_id _)
  rw [h2] at h
  rw [← h]
  rfl

theorem hφpt_nsmul (hc : L.IsCommutative) (m : ℕ) (z : Multiplicative (L.AlgPoints hc k)) :
    RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (powMonoidHom m z)) =
      CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m)
        (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd z)) := by
  rw [mapPt_schemeNsmul, powMonoidHom_apply, toAdd_pow, RelativeGroupLaw.AlgPoints.toPoint_nsmul]

theorem hφpt_neg (hc : L.IsCommutative) (z : Multiplicative (L.AlgPoints hc k)) :
    RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (invMonoidHom z)) =
      CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L)
        (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd z)) := by
  rw [mapPt_negMor, invMonoidHom_apply, toAdd_inv, RelativeGroupLaw.AlgPoints.toPoint_neg]

theorem isInvertible_of_iso {M N : A.Modules} (e : M ≅ N) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.IsInvertible N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 x
  exact ⟨U, hxU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

def tpowPullbackIso {X Y : Scheme.{0}} (φ : X ⟶ Y) (M : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback φ).obj (Scheme.Modules.tpow M n) ≅ Scheme.Modules.tpow ((Scheme.Modules.pullback φ).obj M) n
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso φ
  | n + 1 => Scheme.Modules.pullbackTensorObjIso φ (Scheme.Modules.tpow M n) M ≪≫ (tpowPullbackIso φ M n ⊗ᵢ Iso.refl _)

def tpowCongr {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N) : ∀ n : ℕ, Scheme.Modules.tpow M n ≅ Scheme.Modules.tpow N n
  | 0 => Iso.refl _
  | n + 1 => tpowCongr e n ⊗ᵢ e

theorem nonempty_iso_pullback_schemeNsmul_tpow_tensor
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛₀ : A.Modules) (a b m : ℕ) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul m)).obj
        (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor f L)).obj 𝓛₀) b) ≅
      Scheme.Modules.tpow ((Scheme.Modules.pullback (L.schemeNsmul m)).obj 𝓛₀) a ⊗
        Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor f L)).obj
          ((Scheme.Modules.pullback (L.schemeNsmul m)).obj 𝓛₀)) b) := by

  let inner : (Scheme.Modules.pullback (L.schemeNsmul m)).obj ((Scheme.Modules.pullback (Polarisation.negMor f L)).obj 𝓛₀) ≅
      (Scheme.Modules.pullback (Polarisation.negMor f L)).obj ((Scheme.Modules.pullback (L.schemeNsmul m)).obj 𝓛₀) :=
    (Scheme.Modules.pullbackComp (L.schemeNsmul m) (Polarisation.negMor f L)).app 𝓛₀ ≪≫
      (Scheme.Modules.pullbackCongr (Polarisation.schemeNsmul_comp_negMor L hc m)).app 𝓛₀ ≪≫
      ((Scheme.Modules.pullbackComp (Polarisation.negMor f L) (L.schemeNsmul m)).app 𝓛₀).symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (tpowPullbackIso (L.schemeNsmul m) 𝓛₀ a ⊗ᵢ
      (tpowPullbackIso (L.schemeNsmul m) _ b ≪≫ tpowCongr inner b))⟩

theorem exists_lift_pullback_schemeNsmul
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (m : ℕ) (z₁ : L.AlgPoints hc k)
    (hz : m • (m • z₁) = 0) :
    ∃ G : RiemannForm.thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul m)).obj 𝓛₀),
      RiemannForm.thetaGroup.pt f L hc _ G = Multiplicative.ofAdd z₁ := by
  obtain ⟨β⟩ := RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso k f L hc hA 𝓛₀ h𝓛₀ m (m • z₁) hz
  have hcomm := (RiemannForm.schemeNsmul_mul_and_translation_comp_schemeNsmul k f L hc m m z₁).2
  let φ : (Scheme.Modules.pullback (RiemannForm.translation f L (RelativeGroupLaw.AlgPoints.toPoint z₁))).obj
      ((Scheme.Modules.pullback (L.schemeNsmul m)).obj 𝓛₀) ≅ (Scheme.Modules.pullback (L.schemeNsmul m)).obj 𝓛₀ :=
    (Scheme.Modules.pullbackComp (RiemannForm.translation f L (RelativeGroupLaw.AlgPoints.toPoint z₁)) (L.schemeNsmul m)).app 𝓛₀ ≪≫
      (Scheme.Modules.pullbackCongr hcomm).app 𝓛₀ ≪≫
      ((Scheme.Modules.pullbackComp (L.schemeNsmul m)
        (RiemannForm.translation f L (RelativeGroupLaw.AlgPoints.toPoint (m • z₁)))).app 𝓛₀).symm ≪≫ β
  exact ⟨RiemannForm.thetaGroup.liftOfIso f L hc _ z₁ φ, RiemannForm.thetaGroup.pt_liftOfIso f L hc _ z₁ φ⟩

theorem exists_monoidHom_tpow_tensor (k : Type) [Field k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (M₁ M₂ : A.Modules) (a b : ℕ) (hab : 1 ≤ a + b) :
    ∃ τ : MonoidHom.eqLocus
          ((thetaGroup.pt f L hc M₁).comp (MonoidHom.fst (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))
          ((thetaGroup.pt f L hc M₂).comp (MonoidHom.snd (thetaGroup f L hc M₁) (thetaGroup f L hc M₂))) →*
        thetaGroup f L hc (Scheme.Modules.tpow M₁ a ⊗ Scheme.Modules.tpow M₂ b),
      (∀ p, thetaGroup.pt f L hc _ (τ p) = thetaGroup.pt f L hc M₁ p.1.1) ∧
      (∀ p (c₁ c₂ : k), thetaGroup.IsScalarElt f L hc M₁ p.1.1 c₁ → thetaGroup.IsScalarElt f L hc M₂ p.1.2 c₂ →
        thetaGroup.IsScalarElt f L hc _ (τ p) (c₁ ^ a * c₂ ^ b)) := by
  exact TgTpow.tpow_tensor_hom f L hc M₁ M₂ a b hab

theorem comm_inv_inv {G : Type} [Group G] (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hcomm : ∀ g h : G, ⁅g, h⁆ ∈ Z) (g h : G) : ⁅g⁻¹, h⁻¹⁆ = ⁅g, h⁆ := by
  obtain ⟨-, hmulL, hmulR, -, -, -⟩ :=
    Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center Z hZ hcomm
  have h1 : ⁅g⁻¹, h⁻¹⁆ * ⁅g, h⁻¹⁆ = 1 := by rw [← hmulL, inv_mul_cancel, commutatorElement_one_left]
  have h2 : ⁅g, h⁻¹⁆ * ⁅g, h⁆ = 1 := by rw [← hmulR, inv_mul_cancel, commutatorElement_one_right]
  rw [eq_inv_of_mul_eq_one_left h1, eq_inv_of_mul_eq_one_left h2, inv_inv]

theorem isScalarElt_pow (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (g : thetaGroup f L hc M) (e : k) (hg : thetaGroup.IsScalarElt f L hc M g e) (n : ℕ) :
    thetaGroup.IsScalarElt f L hc M (g ^ n) (e ^ n) := by
  obtain ⟨-, hmul, hone, -⟩ := thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul k f L hc hA M hM
  induction n with
  | zero => simpa using hone
  | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih hg

end K79COMM

open K79COMM in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓛 𝓛₀ : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (a b : ℕ) (hab : 1 ≤ a + b) (hm : ((a + b : ℕ) : k) ≠ 0)
    (ι : 𝓛 ≅ Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor f L)).obj 𝓛₀) b)
    (g₁ g₂ : thetaGroup f L hc 𝓛)
    (hP : (a + b) • Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₁) = 0)
    (hQ : (a + b) • Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₂) = 0)
    (c : k) (h : thetaGroup.IsScalarElt f L hc 𝓛 ⁅g₁, g₂⁆ c) :
    IsLevelPairingValue f L 𝓛₀ (a + b)
      (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₁)))
      (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₂))) c := by
  classical

  set x := Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₁) with hx
  set y := Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₂) with hy
  obtain ⟨x₁, hx₁⟩ := RelativeGroupLaw.AlgPoints.exists_nsmul_eq_of_isAlgClosed k f L hc hA (a + b) hm x
  obtain ⟨y₁, hy₁⟩ := RelativeGroupLaw.AlgPoints.exists_nsmul_eq_of_isAlgClosed k f L hc hA (a + b) hm y

  let 𝓜 : A.Modules := (Scheme.Modules.pullback (L.schemeNsmul (a + b))).obj 𝓛₀
  let 𝓜n : A.Modules := (Scheme.Modules.pullback (Polarisation.negMor f L)).obj 𝓜
  let 𝓝 : A.Modules := Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓜n b
  have h𝓜 : Scheme.Modules.IsInvertible 𝓜 := h𝓛₀.pullback _
  have h𝓜n : Scheme.Modules.IsInvertible 𝓜n := h𝓜.pullback _
  obtain ⟨ιPB⟩ := nonempty_iso_pullback_schemeNsmul_tpow_tensor k f L hc 𝓛₀ a b (a + b)
  let ιm : (Scheme.Modules.pullback (L.schemeNsmul (a + b))).obj 𝓛 ≅ 𝓝 :=
    (Scheme.Modules.pullback (L.schemeNsmul (a + b))).mapIso ι ≪≫ ιPB
  have h𝓝 : Scheme.Modules.IsInvertible 𝓝 := isInvertible_of_iso ιm (h𝓛.pullback _)

  obtain ⟨Ψ, hΨpt, hΨsc⟩ := thetaGroup.exists_monoidHom_pullback_pt_eq_and_isScalarElt k f f L hc L hc
    (L.schemeNsmul (a + b)) (L.schemeNsmul_over (a + b))
    (fun t P Q => RelativeGroupLaw.mapPt_schemeNsmul_mul L hc (a + b) t P Q)
    (powMonoidHom (a + b)) (hφpt_nsmul L hc (a + b)) 𝓛
  have hp₁ : (g₁, Multiplicative.ofAdd x₁) ∈ MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓛).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      ((powMonoidHom (a + b)).comp (MonoidHom.snd (thetaGroup f L hc 𝓛) _)) := by
    show thetaGroup.pt f L hc 𝓛 g₁ = (Multiplicative.ofAdd x₁) ^ (a + b)
    rw [← ofAdd_nsmul, hx₁, hx, ofAdd_toAdd]
  have hp₂ : (g₂, Multiplicative.ofAdd y₁) ∈ MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓛).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      ((powMonoidHom (a + b)).comp (MonoidHom.snd (thetaGroup f L hc 𝓛) _)) := by
    show thetaGroup.pt f L hc 𝓛 g₂ = (Multiplicative.ofAdd y₁) ^ (a + b)
    rw [← ofAdd_nsmul, hy₁, hy, ofAdd_toAdd]
  let p₁ : ↥(MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓛).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      ((powMonoidHom (a + b)).comp (MonoidHom.snd (thetaGroup f L hc 𝓛) _))) := ⟨_, hp₁⟩
  let p₂ : ↥(MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓛).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      ((powMonoidHom (a + b)).comp (MonoidHom.snd (thetaGroup f L hc 𝓛) _))) := ⟨_, hp₂⟩
  have hcomm₁ : thetaGroup.IsScalarElt f L hc _ ⁅Ψ p₁, Ψ p₂⁆ c := by
    rw [← map_commutatorElement]
    refine hΨsc ⁅p₁, p₂⁆ c ?_ ?_
    · exact h
    · show ⁅Multiplicative.ofAdd x₁, Multiplicative.ofAdd y₁⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

  obtain ⟨τ, hτpt, hτsc⟩ := thetaGroup.exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso k f L hc _ 𝓝 ιm
  have hcomm₂ : thetaGroup.IsScalarElt f L hc 𝓝 ⁅τ (Ψ p₁), τ (Ψ p₂)⁆ c := by
    rw [← map_commutatorElement]; exact (hτsc _ c).mp hcomm₁

  have hxx : (a + b) • ((a + b) • x₁) = 0 := by rw [hx₁]; exact hP
  have hyy : (a + b) • ((a + b) • y₁) = 0 := by rw [hy₁]; exact hQ
  obtain ⟨Gx, hGx⟩ := exists_lift_pullback_schemeNsmul k f L hc hA 𝓛₀ h𝓛₀ (a + b) x₁ hxx
  obtain ⟨Gy, hGy⟩ := exists_lift_pullback_schemeNsmul k f L hc hA 𝓛₀ h𝓛₀ (a + b) y₁ hyy
  obtain ⟨Gnx, hGnx⟩ := exists_lift_pullback_schemeNsmul k f L hc hA 𝓛₀ h𝓛₀ (a + b) (-x₁)
    (by rw [smul_neg, smul_neg, hxx, neg_zero])
  obtain ⟨Gny, hGny⟩ := exists_lift_pullback_schemeNsmul k f L hc hA 𝓛₀ h𝓛₀ (a + b) (-y₁)
    (by rw [smul_neg, smul_neg, hyy, neg_zero])

  obtain ⟨Ψn, hΨnpt, hΨnsc⟩ := thetaGroup.exists_monoidHom_pullback_pt_eq_and_isScalarElt k f f L hc L hc
    (Polarisation.negMor f L) (Polarisation.negMor_over f L)
    (fun t P Q => Polarisation.mapPt_negMor_mul L hc t P Q)
    invMonoidHom (hφpt_neg L hc) 𝓜
  have hq₁ : (Gnx, Multiplicative.ofAdd x₁) ∈ MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      (invMonoidHom.comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _)) := by
    show thetaGroup.pt f L hc 𝓜 Gnx = (Multiplicative.ofAdd x₁)⁻¹
    rw [hGnx, ofAdd_neg]
  have hq₂ : (Gny, Multiplicative.ofAdd y₁) ∈ MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      (invMonoidHom.comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _)) := by
    show thetaGroup.pt f L hc 𝓜 Gny = (Multiplicative.ofAdd y₁)⁻¹
    rw [hGny, ofAdd_neg]
  let q₁ : ↥(MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      (invMonoidHom.comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _))) := ⟨_, hq₁⟩
  let q₂ : ↥(MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (Multiplicative (L.AlgPoints hc k))))
      (invMonoidHom.comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _))) := ⟨_, hq₂⟩

  obtain ⟨ρ, hρpt, hρsc⟩ := exists_monoidHom_tpow_tensor k f L hc 𝓜 𝓜n a b hab
  have hr₁ : (Gx, Ψn q₁) ∈ MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (thetaGroup f L hc 𝓜n)))
      ((thetaGroup.pt f L hc 𝓜n).comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _)) := by
    show thetaGroup.pt f L hc 𝓜 Gx = thetaGroup.pt f L hc 𝓜n (Ψn q₁)
    rw [hGx, hΨnpt]
  have hr₂ : (Gy, Ψn q₂) ∈ MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (thetaGroup f L hc 𝓜n)))
      ((thetaGroup.pt f L hc 𝓜n).comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _)) := by
    show thetaGroup.pt f L hc 𝓜 Gy = thetaGroup.pt f L hc 𝓜n (Ψn q₂)
    rw [hGy, hΨnpt]
  let r₁ : ↥(MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (thetaGroup f L hc 𝓜n)))
      ((thetaGroup.pt f L hc 𝓜n).comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _))) := ⟨_, hr₁⟩
  let r₂ : ↥(MonoidHom.eqLocus
      ((thetaGroup.pt f L hc 𝓜).comp (MonoidHom.fst _ (thetaGroup f L hc 𝓜n)))
      ((thetaGroup.pt f L hc 𝓜n).comp (MonoidHom.snd (thetaGroup f L hc 𝓜) _))) := ⟨_, hr₂⟩

  obtain ⟨hZ𝓝, hC𝓝⟩ := thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker k f L hc hA 𝓝 h𝓝
  obtain ⟨hsame𝓝, -, -, -, -, -⟩ :=
    Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center _ hZ𝓝 hC𝓝
  have e₁ : thetaGroup.pt f L hc 𝓝 (τ (Ψ p₁)) = Multiplicative.ofAdd x₁ := by rw [hτpt, hΨpt]
  have e₂ : thetaGroup.pt f L hc 𝓝 (τ (Ψ p₂)) = Multiplicative.ofAdd y₁ := by rw [hτpt, hΨpt]
  have e₃ : thetaGroup.pt f L hc 𝓝 (ρ r₁) = Multiplicative.ofAdd x₁ := by rw [hρpt]; exact hGx
  have e₄ : thetaGroup.pt f L hc 𝓝 (ρ r₂) = Multiplicative.ofAdd y₁ := by rw [hρpt]; exact hGy
  have hk₁ : (τ (Ψ p₁))⁻¹ * ρ r₁ ∈ (thetaGroup.pt f L hc 𝓝).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e₁, e₃, inv_mul_cancel]
  have hk₂ : (τ (Ψ p₂))⁻¹ * ρ r₂ ∈ (thetaGroup.pt f L hc 𝓝).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e₂, e₄, inv_mul_cancel]
  have hKeq : ⁅τ (Ψ p₁), τ (Ψ p₂)⁆ = ⁅ρ r₁, ρ r₂⁆ := hsame𝓝 _ _ _ _ hk₁ hk₂
  have hcomm₃ : thetaGroup.IsScalarElt f L hc 𝓝 ⁅ρ r₁, ρ r₂⁆ c := hKeq ▸ hcomm₂

  obtain ⟨hZ𝓜, hC𝓜⟩ := thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker k f L hc hA 𝓜 h𝓜
  obtain ⟨huniq𝓜, -, -, -⟩ := thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul k f L hc hA 𝓜 h𝓜
  obtain ⟨e, he, -⟩ := huniq𝓜 ⁅Gx, Gy⁆ (hC𝓜 Gx Gy)
  have hnn : ⁅Gnx, Gny⁆ = ⁅Gx, Gy⁆ := by
    obtain ⟨hsame𝓜, -, -, -, -, -⟩ :=
      Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center _ hZ𝓜 hC𝓜
    have hk₃ : Gnx⁻¹ * Gx⁻¹ ∈ (thetaGroup.pt f L hc 𝓜).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_inv, hGnx, hGx, ofAdd_neg, inv_mul_cancel]
    have hk₄ : Gny⁻¹ * Gy⁻¹ ∈ (thetaGroup.pt f L hc 𝓜).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_inv, hGny, hGy, ofAdd_neg, inv_mul_cancel]
    rw [hsame𝓜 Gnx Gx⁻¹ Gny Gy⁻¹ hk₃ hk₄, comm_inv_inv _ hZ𝓜 hC𝓜]
  have heneg : thetaGroup.IsScalarElt f L hc 𝓜n ⁅Ψn q₁, Ψn q₂⁆ e := by
    rw [← map_commutatorElement]
    refine hΨnsc ⁅q₁, q₂⁆ e ?_ ?_
    · show thetaGroup.IsScalarElt f L hc 𝓜 ⁅Gnx, Gny⁆ e
      rw [hnn]; exact he
    · show ⁅Multiplicative.ofAdd x₁, Multiplicative.ofAdd y₁⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hK : thetaGroup.IsScalarElt f L hc 𝓝 ⁅ρ r₁, ρ r₂⁆ (e ^ a * e ^ b) := by
    rw [← map_commutatorElement]
    exact hρsc ⁅r₁, r₂⁆ e e he heneg

  obtain ⟨huniq𝓝, -, -, -⟩ := thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul k f L hc hA 𝓝 h𝓝
  have hce : c = e ^ (a + b) := by
    rw [pow_add]; exact (huniq𝓝 _ (hC𝓝 _ _)).unique hcomm₃ hK

  have hxT : translation f L (RelativeGroupLaw.AlgPoints.toPoint x) ≫ L.schemeNsmul (a + b) = L.schemeNsmul (a + b) :=
    translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc x (a + b) hP
  have hLL : ⁅levelLift f L hc 𝓛₀ (a + b) x hxT, Gy⁆ = ⁅Gx, Gy⁆ ^ (a + b) := by
    obtain ⟨hsame𝓜, -, -, -, -, hpow⟩ :=
      Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center _ hZ𝓜 hC𝓜
    have hk₅ : (levelLift f L hc 𝓛₀ (a + b) x hxT)⁻¹ * Gx ^ (a + b) ∈ (thetaGroup.pt f L hc 𝓜).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, pt_levelLift, hGx, ← ofAdd_nsmul, hx₁, inv_mul_cancel]
    have hk₆ : Gy⁻¹ * Gy ∈ (thetaGroup.pt f L hc 𝓜).ker := by rw [inv_mul_cancel]; exact one_mem _
    rw [hsame𝓜 (levelLift f L hc 𝓛₀ (a + b) x hxT) (Gx ^ (a + b)) Gy Gy hk₅ hk₆, (hpow Gx Gy (a + b)).1]
  have hscal : thetaGroup.IsScalarElt f L hc 𝓜 ⁅levelLift f L hc 𝓛₀ (a + b) x hxT, Gy⁆ c := by
    rw [hLL, hce]; exact isScalarElt_pow k f L hc hA 𝓜 h𝓜 _ e he (a + b)

  have key := (thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift k f L hc 𝓛₀ (a + b) x hxT c).1
    Gy hscal
  rwa [hGy, toAdd_ofAdd, hy₁] at key

end
end S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor (solution)
