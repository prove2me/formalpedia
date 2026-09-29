-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.formallyUnramified_of_represents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0aa933b8-0383-5d57-acaf-be7175267de5

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_of_isPullback_of_isPullback_of_three_le
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_isPullback_of_comp_eq_comp_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

noncomputable section

namespace P2mKcQmUnram

section Ext

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
  {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S}

theorem qm_ext {s₁ s₂ : QMStructure Λ star β X} (hact : s₁.act = s₂.act) (hP : s₁.P = s₂.P) : s₁ = s₂ := by
  cases s₁
  cases s₂
  cases hact
  cases hP
  rfl

end Ext

section Comp

variable {g d n : ℕ}

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {u u' : T ⟶ Spec (CommRingCat.of S)} (h : u = u')
    (P Q : SchemeHomOver u f) (P' Q' : SchemeHomOver u' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul u P Q).1 = (L.mul u' P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem spec_map_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S')
    (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem isPullback_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] {φ : S →+* S'}
    {ψ : S' →+* S''} {u : PolarisedAbelianScheme g d n S} {u' : PolarisedAbelianScheme g d n S'}
    {u'' : PolarisedAbelianScheme g d n S''}
    (h : PolarisedAbelianScheme.IsPullback φ u u') (h' : PolarisedAbelianScheme.IsPullback ψ u' u'') :
    PolarisedAbelianScheme.IsPullback (ψ.comp φ) u u'' := by
  obtain ⟨gA, hg, hmul, hP, hpol⟩ := h
  obtain ⟨gB, hgB, hmulB, hPB, hpolB⟩ := h'
  have hc := spec_map_comp φ ψ
  have hsq : CategoryTheory.IsPullback (gB ≫ gA) u''.f u.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hc]
    exact hgB.paste_horiz hg
  refine ⟨gB ≫ gA, hsq, ?_, ?_, ?_⟩
  · intro T t'' x y
    have h1 := congrArg (fun k => k ≫ gA) (hmulB t'' x y)
    simp only [Category.assoc] at h1
    rw [h1, hmul]
    exact mul_val_congr u.L (by rw [Category.assoc, hc]) _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)
  · intro i
    rw [← Category.assoc, hPB, Category.assoc, hP, ← Category.assoc, hc]
  · exact ⟨(Scheme.Modules.pullbackComp gB gA).symm.app u.pol ≪≫
      (Scheme.Modules.pullback gB).mapIso hpol.some ≪≫ hpolB.some⟩

end Comp

theorem one_comp_eq_of_hom {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q)) :
    (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of R)))
  have h := hhom (𝟙 _) (L.one _) (L.one _)
  rw [L.one_mul] at h
  have h1 : pushPt φ hφ (L.one (𝟙 _)) = L.one (𝟙 _) :=
    mul_left_cancel (a := pushPt φ hφ (L.one (𝟙 _))) (h.symm.trans (mul_one _).symm)
  exact congrArg Subtype.val h1

theorem isNilpotent_of_ker_sq {C C₀ : Type} [CommRing C] [CommRing C₀] (q : C →+* C₀)
    (hq : RingHom.ker q ^ 2 = ⊥) (c : C) (hc : q c = 0) : IsNilpotent c :=
  ⟨2, by
    have h : c ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow (by rwa [RingHom.mem_ker]) 2
    rwa [hq, Ideal.mem_bot] at h⟩

section Generator

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
  {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S}

def orb (s : QMStructure Λ star β X) (x : ↥Λ) : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f :=
  pushPt (s.act x) (s.act_over x) s.P

@[scoped simp] theorem orb_coe (s : QMStructure Λ star β X) (x : ↥Λ) : (orb s x).1 = s.P.1 ≫ s.act x := rfl

theorem orb_add (s : QMStructure Λ star β X) (x y : ↥Λ) :
    orb s (x + y) = X.L.mul (𝟙 _) (orb s x) (orb s y) :=
  s.act_add x y (𝟙 _) s.P

theorem orb_zero (s : QMStructure Λ star β X) : orb s 0 = X.L.one (𝟙 _) := by
  letI := X.L.pointGroup (𝟙 (Spec (CommRingCat.of S)))
  have h : orb s 0 = orb s 0 * orb s 0 := by
    have := orb_add s 0 0
    rw [add_zero] at this
    exact this
  exact mul_left_cancel (a := orb s 0) (h.symm.trans (mul_one _).symm)

theorem orb_neg (s : QMStructure Λ star β X) (x : ↥Λ) :
    orb s (-x) = X.L.inv (𝟙 _) (orb s x) := by
  letI := X.L.pointGroup (𝟙 (Spec (CommRingCat.of S)))
  have h : orb s x * orb s (-x) = 1 := by
    have := orb_add s x (-x)
    rw [add_neg_cancel, orb_zero] at this
    exact this.symm
  exact eq_inv_of_mul_eq_one_right h

def agree (s₁ s₂ : QMStructure Λ star β X) : AddSubgroup ↥Λ where
  carrier := {x | orb s₁ x = orb s₂ x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [orb_add, orb_add, hx, hy]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [orb_zero, orb_zero]
  neg_mem' {x} hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [orb_neg, orb_neg, hx]

theorem mem_agree {s₁ s₂ : QMStructure Λ star β X} {x : ↥Λ} : x ∈ agree s₁ s₂ ↔ orb s₁ x = orb s₂ x := Iff.rfl

theorem P_eq (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (s₁ s₂ : QMStructure Λ star β X) : s₁.P = s₂.P := by
  have hβj : ∀ j, β j ∈ agree s₁ s₂ := fun j =>
    (s₁.level_match j).trans (s₂.level_match j).symm
  have hone : (⟨1, h1⟩ : ↥Λ) ∈ agree s₁ s₂ := by
    obtain ⟨c, hc, -⟩ := hβ ⟨1, h1⟩
    rw [hc]
    exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hβj j) (c j)
  rw [mem_agree] at hone
  have h := congrArg Subtype.val hone
  rw [orb_coe, orb_coe, s₁.act_one h1, s₂.act_one h1, Category.comp_id, Category.comp_id] at h
  exact Subtype.ext h

end Generator

section Main

theorem formallyUnramified {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of R))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ)
    (hnat : (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1))
    (hsurj : (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z))
    (hinj : (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'')) :
    FormallyUnramified ζ := by
  refine FormallyUnramified.of_hom_ext ζ fun C C₀ φq hφq hker g₁ g₂ hig hgf => ?_

  obtain ⟨r', hr'⟩ := Spec.map_surjective (g₁ ≫ ζ)
  let r : R →+* ↥C := r'.hom
  have hr : Spec.map (CommRingCat.ofHom r) = g₁ ≫ ζ := by rw [← hr']; rfl
  let z₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom r)) ζ := ⟨g₁, hr.symm⟩
  let z₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom r)) ζ := ⟨g₂, by rw [hr, hgf]⟩

  obtain ⟨XC, hXC⟩ := PolarisedAbelianScheme.exists_isPullback r X
  obtain ⟨s₁, hs₁⟩ := hsurj (↥C) r XC hXC z₁
  obtain ⟨s₂, hs₂⟩ := hsurj (↥C) r XC hXC z₂
  suffices hs : s₁ = s₂ by
    subst hs
    exact congrArg Subtype.val (hs₁.symm.trans hs₂)

  let p : ↥C →+* ↥C₀ := φq.hom
  have hp : Spec.map (CommRingCat.ofHom p) = Spec.map φq := rfl
  obtain ⟨X₀, hX₀⟩ := PolarisedAbelianScheme.exists_isPullback p XC
  have hX₀' : PolarisedAbelianScheme.IsPullback (p.comp r) X X₀ := isPullback_comp hXC hX₀
  obtain ⟨s₁', hs₁'⟩ := QMStructure.exists_isPullback (Λ := Λ) (star := star) (β := β) p hX₀ s₁
  obtain ⟨s₂', hs₂'⟩ := QMStructure.exists_isPullback (Λ := Λ) (star := star) (β := β) p hX₀ s₂
  have h₁ := hnat (↥C) (↥C₀) r (p.comp r) p rfl XC X₀ hXC hX₀' s₁ s₁' hs₁'
  have h₂ := hnat (↥C) (↥C₀) r (p.comp r) p rfl XC X₀ hXC hX₀' s₂ s₂' hs₂'
  rw [hs₁, hp] at h₁
  rw [hs₂, hp] at h₂
  have h12' : s₁' = s₂' :=
    hinj (↥C₀) (p.comp r) X₀ hX₀' s₁' s₂' (Subtype.ext (by
      rw [h₁, h₂]
      exact hig))
  subst h12'

  obtain ⟨gA₁, hg₁, hmul₁, hP₁, hpol₁, hact₁, -⟩ := hs₁'
  obtain ⟨gA₂, hg₂, hmul₂, hP₂, hpol₂, hact₂, -⟩ := hs₂'
  have hunit : IsUnit ((m : ℕ) : ↥C₀) := by simpa using hm'.map (p.comp r)
  have hgA : gA₁ = gA₂ :=
    PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le hm p hunit XC X₀ gA₁ gA₂
      hg₁ hmul₁ hP₁ hpol₁ hg₂ hmul₂ hP₂ hpol₂
  subst hgA

  have hact : s₁.act = s₂.act := by
    funext x
    have hx : gA₁ ≫ s₁.act x = gA₁ ≫ s₂.act x := by rw [← hact₁ x, ← hact₂ x]
    exact XC.bundle.eq_of_one_comp_eq_one_comp_of_isPullback_of_comp_eq_comp_of_isNilpotent XC.L
      (s₁.act x) (s₂.act x) (s₁.act_over x) (s₂.act_over x)
      ((one_comp_eq_of_hom XC.L _ _ (s₁.act_hom x)).trans (one_comp_eq_of_hom XC.L _ _ (s₂.act_hom x)).symm)
      p hφq (isNilpotent_of_ker_sq p hker) gA₁ hg₁ hx

  exact qm_ext hact (P_eq hΛ.isOrder.one_mem hβ s₁ s₂)

end Main

end P2mKcQmUnram
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents.P2mKcQmUnram"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents.P2mKcQmUnram"

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of R))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ)
    (hnat : (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1))
    (hsurj : (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z))
    (hinj : (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'')) :
    FormallyUnramified ζ :=
  P2mKcQmUnram.formallyUnramified hqq' hB Λ hΛ μ hμ star hstar β hβ d m hm R hm' X Z ζ ptZ hnat hsurj hinj

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents (solution)
