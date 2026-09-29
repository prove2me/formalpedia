-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_ptZ_of_isClosedImmersion_iff_qmConditions
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dac7b891-8f1e-5557-bddd-7970ab32b2f8

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_of_isPullback_of_isPullback_of_three_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe"

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM"

noncomputable section

namespace KRep

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}

def toLA {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S} (s : QMStructure Λ star β X) :
    LatticeAction Λ X.f X.L where
  act := s.act
  act_over := s.act_over
  act_hom := s.act_hom
  act_one := s.act_one
  act_mul := s.act_mul
  act_add := s.act_add

@[scoped simp] theorem toLA_act {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S} (s : QMStructure Λ star β X) :
    (toLA s).act = s.act := rfl

theorem QMStructure_ext {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S}
    (s s' : QMStructure Λ star β X) (h : s.act = s'.act) (hP : s.P = s'.P) : s = s' := by
  cases s; cases s'
  cases h; cases hP
  rfl

theorem locIso_congr_left {S' : Type} [CommRing S'] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of S'))
    {M M₁ N : Y.Modules} (e : M ≅ M₁) (h : LocIsoOnBase g M N) : LocIsoOnBase g M₁ N := by
  intro s
  obtain ⟨U, hs, ⟨i⟩⟩ := h s
  exact ⟨U, hs, ⟨((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).mapIso e).symm ≪≫ i⟩⟩

section Model

variable {R : Type} [CommRing R] (X : PolarisedAbelianScheme 2 d m R)
  {T : Type} [CommRing T] {φ : R →+* T} {X' : PolarisedAbelianScheme 2 d m T}

def gA (hX' : PolarisedAbelianScheme.IsPullback φ X X') : X'.A ⟶ X.A := hX'.choose

theorem gA_isPullback (hX' : PolarisedAbelianScheme.IsPullback φ X X') :
    CategoryTheory.IsPullback (gA X hX') X'.f X.f (Spec.map (CommRingCat.ofHom φ)) := hX'.choose_spec.choose

theorem gA_mul (hX' : PolarisedAbelianScheme.IsPullback φ X X')
    {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t' X'.f) :
    (X'.L.mul t' x y).1 ≫ gA X hX' =
      (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨x.1 ≫ gA X hX', by rw [Category.assoc, (gA_isPullback X hX').w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ gA X hX', by rw [Category.assoc, (gA_isPullback X hX').w, ← Category.assoc, y.2]⟩).1 :=
  hX'.choose_spec.choose_spec.1 t' x y

theorem gA_P (hX' : PolarisedAbelianScheme.IsPullback φ X X') (i : Fin (2 * 2)) :
    (X'.P i).1 ≫ gA X hX' = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1 :=
  hX'.choose_spec.choose_spec.2.1 i

theorem gA_pol (hX' : PolarisedAbelianScheme.IsPullback φ X X') :
    Nonempty ((Scheme.Modules.pullback (gA X hX')).obj X.pol ≅ X'.pol) :=
  hX'.choose_spec.choose_spec.2.2

theorem gA_isGroupPullback (hX' : PolarisedAbelianScheme.IsPullback φ X X') :
    IsGroupPullback φ X.L X'.L (gA X hX') :=
  ⟨gA_isPullback X hX', fun t' x y => gA_mul X hX' t' x y⟩

end Model

section QMC

variable (Λ star β)
variable {R : Type} [CommRing R] (X : PolarisedAbelianScheme 2 d m R)

def QMCond (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (i' : LatticeAction Λ f' L') : Prop :=
  (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
      (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
      ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k)) ∧
  (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
    ∀ j : Fin (2 * 2), (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
      Spec.map (CommRingCat.ofHom φ) ≫ (X.P j).1) ∧
  (∃ polE : A'.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f' L' i'.act i'.act_over star polE ∧
      LocIsoOnBase f' ((Scheme.Modules.pullback g).obj X.pol) (polE ⊗ polE ⊗ polE))

variable {Λ star β X}

theorem qmCond_toLA {T : Type} [CommRing T] {φ : R →+* T} {X' : PolarisedAbelianScheme 2 d m T}
    (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' : QMStructure Λ star β X') :
    QMCond Λ star β X T φ X'.L (gA X hX') (toLA s') := by
  refine ⟨?_, ?_, ?_⟩
  · exact s'.act_trace
  · refine ⟨s'.P, fun j => ?_⟩
    have e := congrArg Subtype.val (s'.level_match j)
    change (pushPt (s'.act (β j)) (s'.act_over (β j)) s'.P).1 ≫ gA X hX' = _
    rw [e, gA_P]
  · obtain ⟨polE, hcan, hloc⟩ := s'.pol_canonical
    obtain ⟨e⟩ := gA_pol X hX'
    exact ⟨polE, hcan, locIso_congr_left X'.f e.symm hloc⟩

end QMC

section Generator

variable {S : Type} [CommRing S] {X' : PolarisedAbelianScheme 2 d m S}

@[reducible] def ptGrp (X' : PolarisedAbelianScheme 2 d m S) : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X'.f) :=
  { X'.L.pointGroup (𝟙 (Spec (CommRingCat.of S))) with mul_comm := fun x y => X'.comm _ x y }

theorem P_eq_comb (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (c : Fin (2 * 2) → ℤ) (hc : (⟨1, hone⟩ : ↥Λ) = ∑ j, c j • β j)
    (s : QMStructure Λ star β X') :
    letI := ptGrp X'
    s.P = Additive.toMul (∑ j, c j • Additive.ofMul (X'.P j)) := by
  letI := ptGrp X'
  let F : ↥Λ →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X'.f) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pushPt (s.act x) (s.act_over x) s.P))
      (fun x y => congrArg Additive.ofMul (s.act_add x y _ s.P))
  have hF : ∀ x, F x = Additive.ofMul (pushPt (s.act x) (s.act_over x) s.P) := fun x => rfl
  have h1 : s.P = Additive.toMul (F ⟨1, hone⟩) := by
    rw [hF, toMul_ofMul]
    apply Subtype.ext
    show s.P.1 = s.P.1 ≫ s.act ⟨1, hone⟩
    rw [s.act_one hone, Category.comp_id]
  rw [h1, hc, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, hF, s.level_match j]

theorem eq_of_act_eq (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (s s' : QMStructure Λ star β X') (h : s.act = s'.act) : s = s' := by
  obtain ⟨c, hc, -⟩ := hβ ⟨1, hone⟩
  apply QMStructure_ext s s' h
  have e1 := P_eq_comb hone c hc s
  have e2 := P_eq_comb hone c hc s'
  exact e1.trans e2.symm

end Generator

end KRep
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions.KRep"

namespace ActionBC
theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (e : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst e
  have h1 : P₁ = P₂ := Subtype.ext hP
  have h2 : Q₁ = Q₂ := Subtype.ext hQ
  subst h1 h2
  rfl
end ActionBC
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions.KRep"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions.KRep"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE)
    (hE : RepresentsLatticeActions Λ X.L E πE cl)
    (Z : Scheme.{0}) (ι : Z ⟶ E) (hι : IsClosedImmersion ι)
    (hZ : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        ((∃ y : Spec (CommRingCat.of R') ⟶ Z, y ≫ ι = (cl R' φ L' g hg i').1) ↔
          ((∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k)
              (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
              Function.Injective τ →
              (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
              (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
              (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
              ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
              ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
                LinearMap.trace k V Φ = (n : k)) ∧
          (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
            ∀ j : Fin (2 * 2), (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
              Spec.map (CommRingCat.ofHom φ) ≫ (X.P j).1) ∧
          (∃ polE : A'.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f' L' i'.act i'.act_over star polE ∧
              LocIsoOnBase f' ((Scheme.Modules.pullback g).obj X.pol) (polE ⊗ polE ⊗ polE))))) :
    ∃ (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ι ≫ πE)),

      (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ι ≫ πE)),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'')  := by
  haveI : Mono ι := inferInstance
  have hone : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.1.one_mem

  have hZ' : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ X X') (i' : LatticeAction Λ X'.f X'.L),
      (∃ y : Spec (CommRingCat.of T) ⟶ Z, y ≫ ι = (cl T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') i').1) ↔
        KRep.QMCond Λ star β X T φ X'.L (KRep.gA X hX') i' :=
    fun T _ φ X' hX' i' => hZ T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') i'

  have hex : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' : QMStructure Λ star β X'),
      ∃ y : Spec (CommRingCat.of T) ⟶ Z,
        y ≫ ι = (cl T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') (KRep.toLA s')).1 :=
    fun T _ φ X' hX' s' => (hZ' T φ X' hX' (KRep.toLA s')).mpr (KRep.qmCond_toLA hX' s')
  let ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
      PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
        SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ι ≫ πE) :=
    fun T _ φ X' hX' s' => ⟨(hex T φ X' hX' s').choose, by
      rw [← Category.assoc, (hex T φ X' hX' s').choose_spec]
      exact (cl T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') (KRep.toLA s')).2⟩
  have ptZ_ι : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' : QMStructure Λ star β X'),
      (ptZ T φ X' hX' s').1 ≫ ι = (cl T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') (KRep.toLA s')).1 :=
    fun T _ φ X' hX' s' => (hex T φ X' hX' s').choose_spec
  refine ⟨ptZ, ?_, ?_, ?_⟩
  ·
    intro T T' _ _ φ φ' ψ hψ X' X'' hX' hX'' s' s'' hss
    subst hψ
    obtain ⟨h, hh, hmul, hlev, hpol, hact, hPP⟩ := hss
    rw [← cancel_mono ι, Category.assoc, ptZ_ι, ptZ_ι]

    have hSpec : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcart : CategoryTheory.IsPullback (h ≫ KRep.gA X hX') X''.f X.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
      rw [hSpec]
      exact IsPullback.paste_horiz hh (KRep.gA_isPullback X hX')
    have hmul2 : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver t' X''.f),
        (X''.L.mul t' x y).1 ≫ (h ≫ KRep.gA X hX') =
          (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (ψ.comp φ)))
            ⟨x.1 ≫ (h ≫ KRep.gA X hX'), by rw [Category.assoc, hcart.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ (h ≫ KRep.gA X hX'), by rw [Category.assoc, hcart.w, ← Category.assoc, y.2]⟩).1 := by
      intro T₀ t' x y
      rw [← Category.assoc, hmul, KRep.gA_mul]
      refine ActionBC.mul_val_congr (by rw [hSpec, Category.assoc]) _ _ _ _ ?_ ?_
      · show (x.1 ≫ h) ≫ KRep.gA X hX' = x.1 ≫ h ≫ KRep.gA X hX'
        exact Category.assoc _ _ _
      · show (y.1 ≫ h) ≫ KRep.gA X hX' = y.1 ≫ h ≫ KRep.gA X hX'
        exact Category.assoc _ _ _
    have hgg : KRep.gA X hX'' = h ≫ KRep.gA X hX' := by
      refine AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le hm (ψ.comp φ)
        (by simpa using hm'.map (ψ.comp φ)) X X'' _ _
        (KRep.gA_isPullback X hX'') (fun t' x y => KRep.gA_mul X hX'' t' x y) (KRep.gA_P X hX'') (KRep.gA_pol X hX'')
        hcart (fun t' x y => hmul2 t' x y) ?_ ?_
      · intro i
        rw [← Category.assoc, hlev, Category.assoc, KRep.gA_P, ← Category.assoc, ← hSpec]
      · obtain ⟨e₁⟩ := KRep.gA_pol X hX'
        obtain ⟨e₂⟩ := hpol
        exact ⟨((Scheme.Modules.pullbackComp h (KRep.gA X hX')).app X.pol).symm ≪≫
          (Scheme.Modules.pullback h).mapIso e₁ ≪≫ e₂⟩

    have key : ∀ (g'' : X''.A ⟶ X.A) (hg'' : IsGroupPullback (ψ.comp φ) X.L X''.L g''), g'' = h ≫ KRep.gA X hX' →
        (cl T' (ψ.comp φ) X''.L g'' hg'' (KRep.toLA s'')).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (cl T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') (KRep.toLA s')).1 := by
      intro g'' hg'' e
      subst e
      exact hE.cl_comp T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') (KRep.toLA s') T' ψ X''.L
        (h ≫ KRep.gA X hX') hg'' (KRep.toLA s'') h ⟨hh, hmul⟩ rfl hact
    exact key _ _ hgg
  ·
    intro T _ φ X' hX' z
    let pt : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE := ⟨z.1 ≫ ι, by rw [Category.assoc]; exact z.2⟩
    obtain ⟨i', hi'⟩ := hE.cl_surjective T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') pt
    obtain ⟨htr, ⟨P, hP⟩, ⟨polE, hcan, hloc⟩⟩ := (hZ' T φ X' hX' i').mp ⟨z.1, by rw [hi']⟩
    obtain ⟨e⟩ := KRep.gA_pol X hX'
    let s' : QMStructure Λ star β X' :=
      { act := i'.act
        act_over := i'.act_over
        act_hom := i'.act_hom
        act_one := i'.act_one
        act_mul := i'.act_mul
        act_add := i'.act_add
        act_trace := htr
        P := P
        level_match := fun j => by
          apply Subtype.ext
          apply (KRep.gA_isPullback X hX').hom_ext
          · rw [hP j, KRep.gA_P]
          · rw [(pushPt (i'.act (β j)) (i'.act_over (β j)) P).2, (X'.P j).2]
        pol_canonical := ⟨polE, hcan, KRep.locIso_congr_left X'.f e hloc⟩ }
    refine ⟨s', ?_⟩
    have hla : KRep.toLA s' = i' := LatticeAction.ext rfl
    apply Subtype.ext
    rw [← cancel_mono ι, ptZ_ι, hla, hi']
  ·
    intro T _ φ X' hX' s' s'' heq
    have e1 := ptZ_ι T φ X' hX' s'
    rw [heq, ptZ_ι] at e1
    have e2 := hE.cl_injective T φ X'.L (KRep.gA X hX') (KRep.gA_isGroupPullback X hX') (KRep.toLA s'') (KRep.toLA s')
      (Subtype.ext e1)
    exact (KRep.eq_of_act_eq hone hβ s'' s' (by simpa using congrArg LatticeAction.act e2)).symm

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions (solution)
