-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.exists_isRiemannForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3cd43c01-7818-5cc2-96b7-bd42f01c10b9

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isLevelPairingValue
import Theorems.Thm_AlgebraicGeometry_RiemannForm_pow_eq_one_of_isLevelPairingValue
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_add_left_and_add_right
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_isRiemannForm
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation CategoryTheory.Pseudofunctor.CoGrothendieck.isIso_homMk"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.fibration_map_toFunctor CategoryTheory.Pseudofunctor.CoGrothendieck.homMk_base CategoryTheory.Pseudofunctor.CoGrothendieck.isoMk_hom AlgebraicGeometry.RiemannForm.thetaGroup.pt_liftOfIso AlgebraicGeometry.RiemannForm.modulePair_fiber AlgebraicGeometry.RiemannForm.pt_levelLift AlgebraicGeometry.RiemannForm.modulePair_base AlgebraicGeometry.RiemannForm.thetaGroup.pt_apply AlgebraicGeometry.RiemannForm.translationIso_hom AlgebraicGeometry.Scheme.Modules.fibration_obj CategoryTheory.Pseudofunctor.CoGrothendieck.homMk_fiber"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace RfExistsBody

section DLog

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ} [NeZero k] {ζ : K}

omit [IsDomain K] in
theorem pow_eq_pow_iff_natCast (h : IsPrimitiveRoot ζ k) (i j : ℕ) :
    ζ ^ i = ζ ^ j ↔ (i : ZMod k) = (j : ZMod k) := by
  have hk : 0 < k := Nat.pos_of_neZero k
  have hmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % k) := fun m => by
    conv_lhs => rw [← Nat.div_add_mod m k, pow_add, pow_mul, h.pow_eq_one, one_pow, one_mul]
  rw [ZMod.natCast_eq_natCast_iff', hmod i, hmod j]
  constructor
  · intro H
    exact h.pow_inj (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) H
  · intro H
    rw [H]

noncomputable def dlog (h : IsPrimitiveRoot ζ k) (w : K) (hw : w ^ k = 1) : ℕ :=
  Classical.choose (h.eq_pow_of_pow_eq_one hw)

theorem pow_dlog (h : IsPrimitiveRoot ζ k) (w : K) (hw : w ^ k = 1) :
    ζ ^ dlog h w hw = w :=
  (Classical.choose_spec (h.eq_pow_of_pow_eq_one hw)).2

end DLog

section PadicLog

variable {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime]
  (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)

theorem toZModPow_eq_natCast_appr (n : ℕ) (c : ℤ_[ℓ]) :
    PadicInt.toZModPow n c = ((c.appr n : ℕ) : ZMod (ℓ ^ n)) := rfl

include hζ in
theorem eq_of_forall_pow_appr_eq (c c' : ℤ_[ℓ])
    (h : ∀ n : ℕ, ζ n ^ (c.appr n) = ζ n ^ (c'.appr n)) : c = c' := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  have := h n
  rwa [pow_eq_pow_iff_natCast (hζ n), ← toZModPow_eq_natCast_appr,
    ← toZModPow_eq_natCast_appr] at this

include hζ in
theorem pow_appr_add (c c' : ℤ_[ℓ]) (n : ℕ) :
    ζ n ^ ((c + c').appr n) = ζ n ^ (c.appr n) * ζ n ^ (c'.appr n) := by
  rw [← pow_add, pow_eq_pow_iff_natCast (hζ n), Nat.cast_add, ← toZModPow_eq_natCast_appr,
    ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, map_add]

include hζ in
theorem pow_appr_mul (c c' : ℤ_[ℓ]) (n : ℕ) :
    ζ n ^ ((c * c').appr n) = (ζ n ^ (c'.appr n)) ^ (c.appr n) := by
  rw [← pow_mul, pow_eq_pow_iff_natCast (hζ n), Nat.cast_mul, ← toZModPow_eq_natCast_appr,
    ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, map_mul, mul_comm]

variable [IsDomain K] (w : ℕ → K) (hw : ∀ n : ℕ, w n ^ (ℓ ^ n) = 1) (ht : ∀ n : ℕ, w (n + 1) ^ ℓ = w n)

noncomputable def logSeq : ℕ → ℤ := fun n => (dlog (hζ n) (w n) (hw n) : ℤ)

include hζℓ ht in
theorem pow_dvd_logSeq_sub (i : ℕ) :
    (ℓ : ℤ) ^ i ∣ logSeq ℓ ζ hζ w hw (i + 1) - logSeq ℓ ζ hζ w hw i := by
  have H : ζ i ^ dlog (hζ (i + 1)) (w (i + 1)) (hw (i + 1)) = ζ i ^ dlog (hζ i) (w i) (hw i) := by
    rw [pow_dlog (hζ i), ← hζℓ i, ← pow_mul, mul_comm, pow_mul, pow_dlog, ht]
  rw [pow_eq_pow_iff_natCast (hζ i)] at H
  have H' := (ZMod.intCast_eq_intCast_iff_dvd_sub (dlog (hζ i) (w i) (hw i) : ℤ)
    (dlog (hζ (i + 1)) (w (i + 1)) (hw (i + 1)) : ℤ) (ℓ ^ i)).mp (by push_cast; exact H.symm)
  simpa [logSeq] using H'

noncomputable def padicLog : ℤ_[ℓ] :=
  PadicInt.ofIntSeq (logSeq ℓ ζ hζ w hw)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ ℓ (pow_dvd_logSeq_sub ℓ ζ hζ hζℓ w hw ht))

theorem toZModPow_padicLog (n : ℕ) :
    PadicInt.toZModPow n (padicLog ℓ ζ hζ hζℓ w hw ht)
      = ((dlog (hζ n) (w n) (hw n) : ℕ) : ZMod (ℓ ^ n)) := by
  have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (logSeq ℓ ζ hζ w hw) ℓ
    (pow_dvd_logSeq_sub ℓ ζ hζ hζℓ w hw ht) n
  rw [padicLog, this, logSeq, Int.cast_natCast]

theorem pow_appr_padicLog (n : ℕ) :
    ζ n ^ ((padicLog ℓ ζ hζ hζℓ w hw ht).appr n) = w n := by
  conv_rhs => rw [← pow_dlog (hζ n) (w n) (hw n)]
  rw [pow_eq_pow_iff_natCast (hζ n), ← toZModPow_eq_natCast_appr, toZModPow_padicLog]

end PadicLog

section Level

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
  (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)

include hℓ in
theorem pow_cast_ne_zero (n : ℕ) : ((ℓ ^ n : ℕ) : k) ≠ 0 := by exact_mod_cast pow_ne_zero n hℓ

omit [IsAlgClosed k] [Fact ℓ.Prime] in
theorem transfer_right {n : ℕ} {P Q Q' : L.AlgPoints hc k} (e : Q = Q') {c : k}
    (h : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q') c := e ▸ h

omit [IsAlgClosed k] [Fact ℓ.Prime] in
theorem transfer_left {n : ℕ} {P P' Q : L.AlgPoints hc k} (e : P = P') {c : k}
    (h : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P') (RelativeGroupLaw.AlgPoints.toPoint Q) c := e ▸ h

noncomputable def lval (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) : k :=
  (existsUnique_isLevelPairingValue k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n) P Q hP hQ).exists.choose

theorem lval_spec (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) :
    IsLevelPairingValue f L 𝓛 (ℓ ^ n) (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q)
      (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ) :=
  (existsUnique_isLevelPairingValue k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n) P Q hP hQ).exists.choose_spec

theorem eq_lval (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) (c : k)
    (h : IsLevelPairingValue f L 𝓛 (ℓ ^ n) (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    c = lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ :=
  (existsUnique_isLevelPairingValue k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n) P Q hP hQ).unique h
    (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ)

theorem lval_pow (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) :
    lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ ^ (ℓ ^ n) = 1 :=
  pow_eq_one_of_isLevelPairingValue k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n) P Q hP hQ _
    (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ)

theorem lval_ne_zero (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) :
    lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ ≠ 0 := by
  intro h
  have := lval_pow k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ
  rw [h, zero_pow (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero)] at this
  exact zero_ne_one this

theorem nsmul_torsion {n : ℕ} (m : ℕ) {P : L.AlgPoints hc k} (hP : (ℓ ^ n) • P = 0) : (ℓ ^ n) • (m • P) = 0 := by
  rw [smul_smul, mul_comm, ← smul_smul, hP, smul_zero]

theorem lval_nsmul_right (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) (m : ℕ) :
    lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P (m • Q) hP (nsmul_torsion k f L hc ℓ m hQ) =
      lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ ^ m := by
  have hBI := fun (Q₁ Q₂ : L.AlgPoints hc k) (h₁ : (ℓ ^ n) • Q₁ = 0) (h₂ : (ℓ ^ n) • Q₂ = 0) =>
    (isLevelPairingValue_add_left_and_add_right k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n)
      P P Q₁ Q₂ hP hP h₁ h₂ (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q₁ hP h₁) (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q₁ hP h₁) (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q₂ hP h₂)
      (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q₁ hP h₁)).2 (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q₂ hP h₂)

  have h0 : lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P ((0 : ℕ) • Q) hP (nsmul_torsion k f L hc ℓ 0 hQ) = 1 := by
    have h00 : (ℓ ^ n) • (0 : L.AlgPoints hc k) = 0 := smul_zero _
    have hsq := hBI 0 0 h00 h00
    rw [add_zero] at hsq
    have hcc := eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P 0 hP h00 _ hsq
    have hc0 := lval_ne_zero k f L hc hA 𝓛 h𝓛 ℓ hℓ n P 0 hP h00
    have h1 : lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P 0 hP h00 = 1 := (mul_eq_left₀ hc0).1 hcc
    have e : (0 : ℕ) • Q = 0 := zero_smul _ _
    calc lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P ((0 : ℕ) • Q) hP (nsmul_torsion k f L hc ℓ 0 hQ) = lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P 0 hP h00 := by
          apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P 0 hP h00; rw [← e]; exact lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P _ hP _
      _ = 1 := h1
  induction m with
  | zero => rw [pow_zero]; exact h0
  | succ m ih =>
    have hstep := hBI (m • Q) Q (nsmul_torsion k f L hc ℓ m hQ) hQ
    rw [ih] at hstep
    have e : m • Q + Q = (m + 1) • Q := (succ_nsmul Q m).symm
    rw [pow_succ]
    symm
    apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P _ hP _
    rw [← e]; exact hstep

theorem lval_nsmul_left (n : ℕ) (P Q : L.AlgPoints hc k) (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0) (m : ℕ) :
    lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n (m • P) Q (nsmul_torsion k f L hc ℓ m hP) hQ =
      lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ ^ m := by
  have hBI := fun (P₁ P₂ : L.AlgPoints hc k) (h₁ : (ℓ ^ n) • P₁ = 0) (h₂ : (ℓ ^ n) • P₂ = 0) =>
    (isLevelPairingValue_add_left_and_add_right k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n)
      P₁ P₂ Q Q h₁ h₂ hQ hQ (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P₁ Q h₁ hQ) (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P₂ Q h₂ hQ) (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P₂ Q h₂ hQ)
      (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P₁ Q h₁ hQ)).1 (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n P₂ Q h₂ hQ)
  have h0 : lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n ((0 : ℕ) • P) Q (nsmul_torsion k f L hc ℓ 0 hP) hQ = 1 := by
    have h00 : (ℓ ^ n) • (0 : L.AlgPoints hc k) = 0 := smul_zero _
    have hsq := hBI 0 0 h00 h00
    rw [add_zero] at hsq
    have hcc := eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n 0 Q h00 hQ _ hsq
    have hc0 := lval_ne_zero k f L hc hA 𝓛 h𝓛 ℓ hℓ n 0 Q h00 hQ
    have h1 : lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n 0 Q h00 hQ = 1 := (mul_eq_left₀ hc0).1 hcc
    have e : (0 : ℕ) • P = 0 := zero_smul _ _
    calc lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n ((0 : ℕ) • P) Q (nsmul_torsion k f L hc ℓ 0 hP) hQ = lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n 0 Q h00 hQ := by
          apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n 0 Q h00 hQ; rw [← e]; exact lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ Q _ hQ
      _ = 1 := h1
  induction m with
  | zero => rw [pow_zero]; exact h0
  | succ m ih =>
    have hstep := hBI (m • P) P (nsmul_torsion k f L hc ℓ m hP) hP
    rw [ih] at hstep
    have e : m • P + P = (m + 1) • P := (succ_nsmul P m).symm
    rw [pow_succ]
    symm
    apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ Q _ hQ
    rw [← e]; exact hstep

end Level

section Tate

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
  (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)

theorem tor (a : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ) : (ℓ ^ n) • ((a : ℕ → L.AlgPoints hc k) n) = 0 := by
  have h__af := TateModule.torsion a n
  simp [Nat.cast_smul_eq_nsmul] at h__af
  exact h__af

theorem compat' (a : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ) :
    ℓ • ((a : ℕ → L.AlgPoints hc k) (n + 1)) = (a : ℕ → L.AlgPoints hc k) n := by
  simpa [Nat.cast_smul_eq_nsmul] using TateModule.compat a n

noncomputable def wseq (a b : TateModule ℓ (L.AlgPoints hc k)) : ℕ → k := fun n =>
  lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n ((a : ℕ → L.AlgPoints hc k) n) ((b : ℕ → L.AlgPoints hc k) n) (tor k f L hc ℓ a n) (tor k f L hc ℓ b n)

theorem wseq_pow (a b : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ) : wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n ^ (ℓ ^ n) = 1 :=
  lval_pow k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _

theorem wseq_tower (a b : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ) :
    wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b (n + 1) ^ ℓ = wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n := by
  unfold wseq

  rw [← lval_nsmul_right k f L hc hA 𝓛 h𝓛 ℓ hℓ (n + 1) _ _ (tor k f L hc ℓ a (n + 1)) (tor k f L hc ℓ b (n + 1)) ℓ]
  have hbn : (ℓ ^ (n + 1)) • ((b : ℕ → L.AlgPoints hc k) n) = 0 := by
    rw [← compat' k f L hc ℓ b n]; exact nsmul_torsion k f L hc ℓ ℓ (tor k f L hc ℓ b (n + 1))

  have e1 : lval k f L hc hA 𝓛 h𝓛 ℓ hℓ (n + 1) ((a : ℕ → L.AlgPoints hc k) (n + 1)) (ℓ • (b : ℕ → L.AlgPoints hc k) (n + 1))
      (tor k f L hc ℓ a (n + 1)) (nsmul_torsion k f L hc ℓ ℓ (tor k f L hc ℓ b (n + 1))) =
      lval k f L hc hA 𝓛 h𝓛 ℓ hℓ (n + 1) ((a : ℕ → L.AlgPoints hc k) (n + 1)) ((b : ℕ → L.AlgPoints hc k) n)
      (tor k f L hc ℓ a (n + 1)) hbn := by
    apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ (n + 1)
    exact transfer_right k f L hc 𝓛 (compat' k f L hc ℓ b n)
      (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ (n + 1) ((a : ℕ → L.AlgPoints hc k) (n + 1)) (ℓ • (b : ℕ → L.AlgPoints hc k) (n + 1))
        (tor k f L hc ℓ a (n + 1)) (nsmul_torsion k f L hc ℓ ℓ (tor k f L hc ℓ b (n + 1))))
  rw [e1]

  symm
  apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ (n + 1)
  have hP : (ℓ ^ n * ℓ) • ((a : ℕ → L.AlgPoints hc k) (n + 1)) = 0 := by rw [← pow_succ]; exact tor k f L hc ℓ a (n + 1)
  have h1 : IsLevelPairingValue f L 𝓛 (ℓ ^ n) (RelativeGroupLaw.AlgPoints.toPoint (ℓ • (a : ℕ → L.AlgPoints hc k) (n + 1)))
      (RelativeGroupLaw.AlgPoints.toPoint ((b : ℕ → L.AlgPoints hc k) n))
      (lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n ((a : ℕ → L.AlgPoints hc k) n) ((b : ℕ → L.AlgPoints hc k) n) (tor k f L hc ℓ a n) (tor k f L hc ℓ b n)) := by
    exact transfer_left k f L hc 𝓛 (compat' k f L hc ℓ a n).symm (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _)
  have := isLevelPairingValue_mul_of_isLevelPairingValue_nsmul k f L hc hA 𝓛 h𝓛 (ℓ ^ n) ℓ
    (by rw [← pow_succ]; exact pow_cast_ne_zero k ℓ hℓ (n + 1)) _ _ hP (tor k f L hc ℓ b n) _ h1
  rwa [← pow_succ] at this

noncomputable def e₀ (a b : TateModule ℓ (L.AlgPoints hc k)) : ℤ_[ℓ] :=
  padicLog ℓ ζ hζ hζℓ (wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b) (wseq_pow k f L hc hA 𝓛 h𝓛 ℓ hℓ a b)
    (wseq_tower k f L hc hA 𝓛 h𝓛 ℓ hℓ a b)

theorem pow_appr_e₀ (a b : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ) :
    ζ n ^ ((e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b).appr n) = wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n :=
  pow_appr_padicLog ℓ ζ hζ hζℓ _ _ _ n

theorem eq_e₀ (a b : TateModule ℓ (L.AlgPoints hc k)) (c : ℤ_[ℓ])
    (hc' : ∀ n : ℕ, ζ n ^ (c.appr n) = wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n) :
    c = e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b :=
  eq_of_forall_pow_appr_eq ℓ ζ hζ _ _ fun n => by rw [hc', pow_appr_e₀]

theorem wseq_eq_of (a b : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ) (P Q : L.AlgPoints hc k)
    (hP : (ℓ ^ n) • P = 0) (hQ : (ℓ ^ n) • Q = 0)
    (ha : (a : ℕ → L.AlgPoints hc k) n = P) (hb : (b : ℕ → L.AlgPoints hc k) n = Q) :
    wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n = lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n P Q hP hQ := by
  unfold wseq; subst ha; subst hb; rfl

theorem e₀_add_left (a a' b : TateModule ℓ (L.AlgPoints hc k)) :
    e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ (a + a') b =
      e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b + e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a' b := by
  symm
  refine eq_e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_add ℓ ζ hζ, pow_appr_e₀, pow_appr_e₀]
  have hsum : ((a + a' : TateModule ℓ (L.AlgPoints hc k)) : ℕ → L.AlgPoints hc k) n =
      (a : ℕ → L.AlgPoints hc k) n + (a' : ℕ → L.AlgPoints hc k) n := by simp
  rw [wseq_eq_of k f L hc hA 𝓛 h𝓛 ℓ hℓ (a + a') b n _ _
    (by rw [smul_add, tor, tor, add_zero]) (tor k f L hc ℓ b n) hsum rfl]
  apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n
  exact (isLevelPairingValue_add_left_and_add_right k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n)
    _ _ _ _ (tor k f L hc ℓ a n) (tor k f L hc ℓ a' n) (tor k f L hc ℓ b n) (tor k f L hc ℓ b n) _ _
    (wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n)
    (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _)).1 (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _)

theorem e₀_add_right (a b b' : TateModule ℓ (L.AlgPoints hc k)) :
    e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a (b + b') =
      e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b + e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b' := by
  symm
  refine eq_e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_add ℓ ζ hζ, pow_appr_e₀, pow_appr_e₀]
  have hsum : ((b + b' : TateModule ℓ (L.AlgPoints hc k)) : ℕ → L.AlgPoints hc k) n =
      (b : ℕ → L.AlgPoints hc k) n + (b' : ℕ → L.AlgPoints hc k) n := by simp
  rw [wseq_eq_of k f L hc hA 𝓛 h𝓛 ℓ hℓ a (b + b') n _ _ (tor k f L hc ℓ a n)
    (by rw [smul_add, tor, tor, add_zero]) rfl hsum]
  apply eq_lval k f L hc hA 𝓛 h𝓛 ℓ hℓ n
  exact (isLevelPairingValue_add_left_and_add_right k f L hc hA 𝓛 h𝓛 (ℓ ^ n) (pow_cast_ne_zero k ℓ hℓ n)
    _ _ _ _ (tor k f L hc ℓ a n) (tor k f L hc ℓ a n) (tor k f L hc ℓ b n) (tor k f L hc ℓ b' n) _
    (wseq k f L hc hA 𝓛 h𝓛 ℓ hℓ a b n) _
    (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _)).2 (lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _)

theorem e₀_smul_left (c : ℤ_[ℓ]) (a b : TateModule ℓ (L.AlgPoints hc k)) :
    e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ (c • a) b = c * e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b := by
  symm
  refine eq_e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_mul ℓ ζ hζ, pow_appr_e₀]
  have hlev : ((c • a : TateModule ℓ (L.AlgPoints hc k)) : ℕ → L.AlgPoints hc k) n =
      (c.appr n) • (a : ℕ → L.AlgPoints hc k) n := by
    rw [TateModule.smul_apply, Nat.cast_smul_eq_nsmul]
  rw [wseq_eq_of k f L hc hA 𝓛 h𝓛 ℓ hℓ (c • a) b n _ _ (nsmul_torsion k f L hc ℓ _ (tor k f L hc ℓ a n))
    (tor k f L hc ℓ b n) hlev rfl, lval_nsmul_left]
  rfl

theorem e₀_smul_right (c : ℤ_[ℓ]) (a b : TateModule ℓ (L.AlgPoints hc k)) :
    e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a (c • b) = c * e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b := by
  symm
  refine eq_e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_mul ℓ ζ hζ, pow_appr_e₀]
  have hlev : ((c • b : TateModule ℓ (L.AlgPoints hc k)) : ℕ → L.AlgPoints hc k) n =
      (c.appr n) • (b : ℕ → L.AlgPoints hc k) n := by
    rw [TateModule.smul_apply, Nat.cast_smul_eq_nsmul]
  rw [wseq_eq_of k f L hc hA 𝓛 h𝓛 ℓ hℓ a (c • b) n _ _ (tor k f L hc ℓ a n)
    (nsmul_torsion k f L hc ℓ _ (tor k f L hc ℓ b n)) rfl hlev, lval_nsmul_right]
  rfl

noncomputable def eLin :
    TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  LinearMap.mk₂ ℤ_[ℓ] (e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ)
    (e₀_add_left k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ)
    (fun c a b => by rw [smul_eq_mul]; exact e₀_smul_left k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ c a b)
    (e₀_add_right k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ)
    (fun c a b => by rw [smul_eq_mul]; exact e₀_smul_right k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ c a b)

theorem eLin_apply (a b : TateModule ℓ (L.AlgPoints hc k)) :
    eLin k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b = e₀ k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ a b := rfl

end Tate

end RfExistsBody

open RfExistsBody in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    ∃ e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],
      IsRiemannForm f L hc 𝓛 ℓ ζ e := by
  refine ⟨eLin k f L hc hA 𝓛 h𝓛 ℓ hℓ ζ hζ hζℓ, fun n a b => ?_⟩
  rw [eLin_apply, pow_appr_e₀]
  exact lval_spec k f L hc hA 𝓛 h𝓛 ℓ hℓ n _ _ _ _

end S_AlgebraicGeometry_RiemannForm_exists_isRiemannForm
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_exists_isRiemannForm (solution)
