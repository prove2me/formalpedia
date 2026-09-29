-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_addMorProd_iso_tensor_of_birigidified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/645f80d3-d410-554a-9542-cc397f44c091

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti"
p2m_attr_erase "simp" "PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory"
noncomputable section

namespace CubeFrame

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

abbrev AO : Over (Spec (CommRingCat.of k)) := Over.mk f

abbrev T : Scheme.{0} := pullback (pullback.fst f f ≫ f) f

theorem tensor3_left : (AO f ⊗ AO f ⊗ AO f).left = pullback f (pullback.fst f f ≫ f) := rfl

noncomputable def frameIso : T f ≅ (AO f ⊗ AO f ⊗ AO f).left :=
  pullbackSymmetry (pullback.fst f f ≫ f) f

@[scoped simp] theorem frameIso_hom_fst : (frameIso f).hom ≫ pullback.fst f (pullback.fst f f ≫ f) = pullback.snd _ _ :=
  pullbackSymmetry_hom_comp_fst _ _

@[scoped simp] theorem frameIso_hom_snd : (frameIso f).hom ≫ pullback.snd f (pullback.fst f f ≫ f) = pullback.fst _ _ :=
  pullbackSymmetry_hom_comp_snd _ _

@[scoped simp] theorem frameIso_inv_fst : (frameIso f).inv ≫ pullback.fst (pullback.fst f f ≫ f) f = pullback.snd _ _ :=
  pullbackSymmetry_inv_comp_fst _ _

@[scoped simp] theorem frameIso_inv_snd : (frameIso f).inv ≫ pullback.snd (pullback.fst f f ≫ f) f = pullback.fst _ _ :=
  pullbackSymmetry_inv_comp_snd _ _

variable (x₀ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)

def pt : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ AO f := Over.homMk x₀.1 x₀.2

@[scoped simp] theorem pt_left : (pt f x₀).left = x₀.1 := rfl

theorem slice₁_raw :
    (lift (toUnit (AO f ⊗ AO f) ≫ pt f x₀) (𝟙 (AO f ⊗ AO f)) : AO f ⊗ AO f ⟶ AO f ⊗ AO f ⊗ AO f).left ≫ (frameIso f).inv =
      pullback.lift (𝟙 (pullback f f)) ((pullback.fst f f ≫ f) ≫ x₀.1)
        (by rw [Category.id_comp, Category.assoc, x₀.2, Category.comp_id]) := by
  apply pullback.hom_ext <;> simp [frameIso, pt, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem slice₂_raw :
    (lift (fst (AO f) (AO f)) (lift (toUnit (AO f ⊗ AO f) ≫ pt f x₀) (snd (AO f) (AO f))) :
        AO f ⊗ AO f ⟶ AO f ⊗ AO f ⊗ AO f).left ≫ (frameIso f).inv =
      pullback.lift (pullback.lift ((pullback.fst f f ≫ f) ≫ x₀.1) (pullback.snd f f)
          (by rw [Category.assoc, x₀.2, Category.comp_id, pullback.condition]))
        (pullback.fst f f) (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, x₀.2, Category.comp_id]) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [frameIso, pt, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · simp [frameIso, pt, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem slice₃_raw :
    (lift (fst (AO f) (AO f)) (lift (snd (AO f) (AO f)) (toUnit (AO f ⊗ AO f) ≫ pt f x₀)) :
        AO f ⊗ AO f ⟶ AO f ⊗ AO f ⊗ AO f).left ≫ (frameIso f).inv =
      pullback.lift (pullback.lift (pullback.snd f f) ((pullback.fst f f ≫ f) ≫ x₀.1)
          (by rw [Category.assoc, x₀.2, Category.comp_id, pullback.condition]))
        (pullback.fst f f) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition]) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [frameIso, pt, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · simp [frameIso, pt, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

variable {f}

def pullbackHomInvIso {X' Y' : Scheme.{0}} (e : X' ≅ Y') (M : X'.Modules) :
    (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback e.inv).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp e.hom e.inv).app M ≪≫ (Scheme.Modules.pullbackCongr e.hom_inv_id).app M ≪≫
    (Scheme.Modules.pullbackId X').app M

def pullbackSliceIso {X' Y' W : Scheme.{0}} (e : X' ≅ Y') (M : X'.Modules) (g : W ⟶ Y') (s : W ⟶ X') (h : g ≫ e.inv = s) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback e.inv).obj M) ≅ (Scheme.Modules.pullback s).obj M :=
  (Scheme.Modules.pullbackComp g e.inv).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

variable (f)

theorem cube_raw (hk : IsAlgClosed k) [IsProper f] [IsIntegral A]
    (x₀ y₀ z₀ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (M : (T f).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h₁ : Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 (pullback f f)) ((pullback.fst f f ≫ f) ≫ x₀.1)
        (by rw [Category.id_comp, Category.assoc, x₀.2, Category.comp_id]))).obj M ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.lift ((pullback.fst f f ≫ f) ≫ y₀.1) (pullback.snd f f)
          (by rw [Category.assoc, y₀.2, Category.comp_id, pullback.condition]))
        (pullback.fst f f) (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, y₀.2, Category.comp_id]))).obj M ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.lift (pullback.snd f f) ((pullback.fst f f ≫ f) ≫ z₀.1)
          (by rw [Category.assoc, z₀.2, Category.comp_id, pullback.condition]))
        (pullback.fst f f) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition]))).obj M ≅ 𝟙_ _)) :
    Nonempty (M ≅ 𝟙_ _) := by
  haveI := hk
  let L : (AO f ⊗ AO f ⊗ AO f).left.Modules := (Scheme.Modules.pullback (frameIso f).inv).obj M
  have hL : Scheme.Modules.IsInvertible L := hM.pullback _
  haveI : IsProper (AO f).hom := inferInstanceAs (IsProper f)
  haveI : IsIntegral (AO f).left := inferInstanceAs (IsIntegral A)
  haveI : IsSeparated (AO f).hom := inferInstance
  haveI : LocallyOfFiniteType (AO f).hom := inferInstance
  haveI : QuasiCompact (AO f).hom := inferInstance
  obtain ⟨e₁⟩ := h₁; obtain ⟨e₂⟩ := h₂; obtain ⟨e₃⟩ := h₃
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_monoidalV2 k
    (AO f) (AO f) (AO f) (pt f x₀) (pt f y₀) (pt f z₀) L hL
    ⟨pullbackSliceIso (frameIso f) M _ _ (slice₁_raw f x₀) ≪≫ e₁⟩
    ⟨pullbackSliceIso (frameIso f) M _ _ (slice₂_raw f y₀) ≪≫ e₂⟩
    ⟨pullbackSliceIso (frameIso f) M _ _ (slice₃_raw f z₀) ≪≫ e₃⟩
  exact ⟨(pullbackHomInvIso (frameIso f) M).symm ≪≫ (Scheme.Modules.pullback (frameIso f).hom).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (frameIso f).hom⟩

end CubeFrame
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified.CubeFrame"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified.CubeFrame"

open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

namespace SP1Aux

variable {X' Y' Z' : Scheme.{0}}

noncomputable def pbEq {a b : X' ⟶ Y'} (h : a = b) (N : Y'.Modules) :
    (Scheme.Modules.pullback a).obj N ≅ (Scheme.Modules.pullback b).obj N := (Scheme.Modules.pullbackCongr h).app N

noncomputable def pbComp (a : X' ⟶ Y') (b : Y' ⟶ Z') (N : Z'.Modules) :
    (Scheme.Modules.pullback (a ≫ b)).obj N ≅ (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj N) :=
  ((Scheme.Modules.pullbackComp a b).app N).symm

noncomputable def pbUnit (a : X' ⟶ Y') (N : Y'.Modules) (e : N ≅ 𝟙_ Y'.Modules) :
    (Scheme.Modules.pullback a).obj N ≅ 𝟙_ X'.Modules :=
  (Scheme.Modules.pullback a).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso a

end SP1Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified.CubeFrame"

open SP1Aux CubeFrame in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ addMor f L) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj 𝓟 ≅
      (Scheme.Modules.pullback
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc]; exact pullback.condition))).obj 𝓟 ⊗
      (Scheme.Modules.pullback
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition))).obj 𝓟) := by
  classical
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  haveI : IsProper f := hA.proper
  haveI : IsIntegral A := hA.isIntegral_of_field

  set m13 := pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ addMor f L) (pullback.snd (pullback.fst f f ≫ f) f)
      (by rw [Category.assoc, addMor_over]; exact pullback.condition) with hm13
  set p13 := pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f) (pullback.snd (pullback.fst f f ≫ f) f)
      (by rw [Category.assoc]; exact pullback.condition) with hp13
  set p23 := pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
      (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) with hp23

  set t₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k)) with ht₀def
  have ht₀ : t₀ = 𝟙 _ := Spec.map_id _
  set O : SchemeHomOver t₀ f := RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k) with hOdef
  have hO : O = L.one t₀ := rfl
  let O' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := ⟨O.1, by rw [O.2, ht₀]⟩
  have hO'1 : O'.1 ≫ f = 𝟙 _ := O'.2

  have hO' : O' = L.one (𝟙 _) := by
    have h := L.one_natural t₀ (𝟙 _) (𝟙 _) (by rw [Category.id_comp, ht₀])
    rw [← hO] at h
    apply Subtype.ext
    rw [← h, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

  let z : A ⟶ pullback f f := pullback.lift (𝟙 A) (f ≫ O'.1) (by rw [Category.id_comp, Category.assoc, hO'1, Category.comp_id])
  let ιA : A ⟶ pullback f t₀ := pullback.lift (𝟙 A) f (by rw [Category.id_comp, ht₀, Category.comp_id])
  have hz : ιA ≫ sliceAt f O = z := by
    apply pullback.hom_ext
    · simp [z, ιA, sliceAt, pullback.lift_fst, pullback.lift_snd]
    · simp [z, ιA, sliceAt, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]
      rfl

  have tz : (Scheme.Modules.pullback z).obj 𝓟 ≅ 𝟙_ _ :=
    pbEq hz.symm 𝓟 ≪≫ pbComp ιA (sliceAt f O) 𝓟 ≪≫ pbUnit ιA _ e₁
  have tz' : (Scheme.Modules.pullback (z ≫ (pullbackSymmetry f f).hom)).obj 𝓟 ≅ 𝟙_ _ :=
    pbComp z _ 𝓟 ≪≫ pbEq hz.symm _ ≪≫ pbComp ιA (sliceAt f O) _ ≪≫ pbUnit ιA _ e₂

  have addMor_def : addMor f L = (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 := rfl
  have E2 : pullback.lift ((pullback.fst f f ≫ f) ≫ O'.1) (pullback.snd f f)
      (by rw [Category.assoc, hO'1, Category.comp_id, pullback.condition]) ≫ addMor f L = pullback.snd f f := by
    set ψ := pullback.lift ((pullback.fst f f ≫ f) ≫ O'.1) (pullback.snd f f)
      (by rw [Category.assoc, hO'1, Category.comp_id, pullback.condition]) with hψ
    have hψb : ψ ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by
      rw [← Category.assoc, hψ, pullback.lift_fst, Category.assoc, hO'1, Category.comp_id]
    have hnat := L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) ψ hψb
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
    have hP₁ : GoodReductionJacobian.schemeHomOverComp ψ hψb ⟨pullback.fst f f, rfl⟩ = L.one (pullback.fst f f ≫ f) := by
      rw [← L.one_natural (𝟙 _) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) (Category.comp_id _), ← hO']
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe]
      rw [hψ, pullback.lift_fst]
    have hP₂ : GoodReductionJacobian.schemeHomOverComp ψ hψb ⟨pullback.snd f f, pullback.condition.symm⟩ =
        ⟨pullback.snd f f, pullback.condition.symm⟩ := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe]
      rw [hψ, pullback.lift_snd]
    rw [hP₁, hP₂, L.one_mul] at hnat
    have := congrArg Subtype.val hnat
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
    rw [addMor_def]
    exact this
  have E3 : pullback.lift (pullback.snd f f) ((pullback.fst f f ≫ f) ≫ O'.1)
      (by rw [Category.assoc, hO'1, Category.comp_id, pullback.condition]) ≫ addMor f L = pullback.snd f f := by
    set ψ := pullback.lift (pullback.snd f f) ((pullback.fst f f ≫ f) ≫ O'.1)
      (by rw [Category.assoc, hO'1, Category.comp_id, pullback.condition]) with hψ
    have hψb : ψ ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by
      rw [← Category.assoc, hψ, pullback.lift_fst, pullback.condition]
    have hnat := L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) ψ hψb
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
    have hP₁ : GoodReductionJacobian.schemeHomOverComp ψ hψb ⟨pullback.fst f f, rfl⟩ =
        ⟨pullback.snd f f, pullback.condition.symm⟩ := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe]
      rw [hψ, pullback.lift_fst]
    have hP₂ : GoodReductionJacobian.schemeHomOverComp ψ hψb ⟨pullback.snd f f, pullback.condition.symm⟩ = L.one (pullback.fst f f ≫ f) := by
      rw [← L.one_natural (𝟙 _) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) (Category.comp_id _), ← hO']
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe]
      rw [hψ, pullback.lift_snd]
    rw [hP₁, hP₂, L.mul_one] at hnat
    have := congrArg Subtype.val hnat
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
    rw [addMor_def]
    exact this

  let s₁ : pullback f f ⟶ pullback (pullback.fst f f ≫ f) f :=
    pullback.lift (𝟙 (pullback f f)) ((pullback.fst f f ≫ f) ≫ O'.1) (by rw [Category.id_comp, Category.assoc, O'.2, Category.comp_id])
  let s₂ : pullback f f ⟶ pullback (pullback.fst f f ≫ f) f :=
    pullback.lift (pullback.lift ((pullback.fst f f ≫ f) ≫ O'.1) (pullback.snd f f)
        (by rw [Category.assoc, O'.2, Category.comp_id, pullback.condition]))
      (pullback.fst f f) (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, O'.2, Category.comp_id])
  let s₃ : pullback f f ⟶ pullback (pullback.fst f f ≫ f) f :=
    pullback.lift (pullback.lift (pullback.snd f f) ((pullback.fst f f ≫ f) ≫ O'.1)
        (by rw [Category.assoc, O'.2, Category.comp_id, pullback.condition]))
      (pullback.fst f f) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition])

  have c1m : s₁ ≫ m13 = addMor f L ≫ z := by
    apply pullback.hom_ext <;> simp [s₁, z, hm13, pullback.lift_fst, pullback.lift_snd, addMor_over, pullback.lift_fst_assoc, pullback.lift_snd_assoc] <;> first | rfl | (rw [← Category.assoc, ← Category.assoc, addMor_over]) | (rw [← Category.assoc, ← Category.assoc, ← pullback.condition]) | skip
  have c1p : s₁ ≫ p13 = pullback.fst f f ≫ z := by
    apply pullback.hom_ext <;> simp [s₁, z, hp13, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have c1q : s₁ ≫ p23 = pullback.snd f f ≫ z := by
    apply pullback.hom_ext <;> simp [s₁, z, hp23, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]
  have c2m : s₂ ≫ m13 = (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext
    · rw [pullbackSymmetry_hom_comp_fst, Category.assoc, hm13, pullback.lift_fst, ← Category.assoc]
      simp only [s₂, pullback.lift_fst]
      exact E2
    · rw [pullbackSymmetry_hom_comp_snd, Category.assoc, hm13, pullback.lift_snd]; simp [s₂, pullback.lift_snd]
  have c2p : s₂ ≫ p13 = pullback.fst f f ≫ z ≫ (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext <;> simp [s₂, z, hp13, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition] <;> first | rfl | (rw [← Category.assoc, ← Category.assoc, addMor_over]) | (rw [← Category.assoc, ← Category.assoc, ← pullback.condition]) | skip
  have c2q : s₂ ≫ p23 = (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext <;> simp [s₂, hp23, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have c3m : s₃ ≫ m13 = (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext
    · rw [pullbackSymmetry_hom_comp_fst, Category.assoc, hm13, pullback.lift_fst, ← Category.assoc]
      simp only [s₃, pullback.lift_fst]
      exact E3
    · rw [pullbackSymmetry_hom_comp_snd, Category.assoc, hm13, pullback.lift_snd]; simp [s₃, pullback.lift_snd]
  have c3p : s₃ ≫ p13 = (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext <;> simp [s₃, hp13, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have c3q : s₃ ≫ p23 = pullback.fst f f ≫ z ≫ (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext <;> simp [s₃, z, hp23, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition] <;> first | rfl | (rw [← Category.assoc, ← Category.assoc, addMor_over]) | (rw [← Category.assoc, ← Category.assoc, ← pullback.condition]) | skip

  set X := (Scheme.Modules.pullback m13).obj 𝓟 with hX
  set Y := (Scheme.Modules.pullback p13).obj 𝓟 with hY
  set Z := (Scheme.Modules.pullback p23).obj 𝓟 with hZ
  have hXi : Scheme.Modules.IsInvertible X := h𝓟.pullback _
  have hYZ : Scheme.Modules.IsInvertible (Y ⊗ Z) := (h𝓟.pullback _).tensor_monoidalV2 (h𝓟.pullback _)
  obtain ⟨D, hD, ⟨eD⟩⟩ := hYZ.exists_tensor_inverse_monoidalV2

  have r1 : (Scheme.Modules.pullback s₁).obj X ≅ (Scheme.Modules.pullback s₁).obj (Y ⊗ Z) :=
    (pbComp s₁ m13 𝓟).symm ≪≫ pbEq c1m 𝓟 ≪≫ pbComp _ z 𝓟 ≪≫ pbUnit _ _ tz ≪≫
      (λ_ (𝟙_ _)).symm ≪≫
      (tensorIso ((pbComp s₁ p13 𝓟).symm ≪≫ pbEq c1p 𝓟 ≪≫ pbComp _ z 𝓟 ≪≫ pbUnit _ _ tz)
        ((pbComp s₁ p23 𝓟).symm ≪≫ pbEq c1q 𝓟 ≪≫ pbComp _ z 𝓟 ≪≫ pbUnit _ _ tz)).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso s₁ Y Z).symm
  have r2 : (Scheme.Modules.pullback s₂).obj X ≅ (Scheme.Modules.pullback s₂).obj (Y ⊗ Z) :=
    (pbComp s₂ m13 𝓟).symm ≪≫ pbEq c2m 𝓟 ≪≫ (λ_ _).symm ≪≫
      (tensorIso ((pbComp s₂ p13 𝓟).symm ≪≫ pbEq c2p 𝓟 ≪≫ pbComp _ (z ≫ (pullbackSymmetry f f).hom) 𝓟 ≪≫ pbUnit _ _ tz')
        ((pbComp s₂ p23 𝓟).symm ≪≫ pbEq c2q 𝓟)).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso s₂ Y Z).symm
  have r3 : (Scheme.Modules.pullback s₃).obj X ≅ (Scheme.Modules.pullback s₃).obj (Y ⊗ Z) :=
    (pbComp s₃ m13 𝓟).symm ≪≫ pbEq c3m 𝓟 ≪≫ (ρ_ _).symm ≪≫
      (tensorIso ((pbComp s₃ p13 𝓟).symm ≪≫ pbEq c3p 𝓟)
        ((pbComp s₃ p23 𝓟).symm ≪≫ pbEq c3q 𝓟 ≪≫ pbComp _ (z ≫ (pullbackSymmetry f f).hom) 𝓟 ≪≫ pbUnit _ _ tz')).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso s₃ Y Z).symm

  have sliceM : ∀ (s : pullback f f ⟶ pullback (pullback.fst f f ≫ f) f),
      ((Scheme.Modules.pullback s).obj X ≅ (Scheme.Modules.pullback s).obj (Y ⊗ Z)) →
      ((Scheme.Modules.pullback s).obj (X ⊗ D) ≅ 𝟙_ _) := fun s r =>
    Scheme.Modules.pullbackTensorObjIso s X D ≪≫ whiskerRightIso r _ ≪≫
      (Scheme.Modules.pullbackTensorObjIso s (Y ⊗ Z) D).symm ≪≫ pbUnit s _ eD
  obtain ⟨eM⟩ := CubeFrame.cube_raw f inferInstance O' O' O' (X ⊗ D) (hXi.tensor_monoidalV2 hD)
    ⟨sliceM s₁ r1⟩ ⟨sliceM s₂ r2⟩ ⟨sliceM s₃ r3⟩

  exact ⟨(ρ_ X).symm ≪≫ whiskerLeftIso X ((β_ _ _ ≪≫ eD).symm) ≪≫ (α_ X D (Y ⊗ Z)).symm ≪≫
    whiskerRightIso eM _ ≪≫ λ_ (Y ⊗ Z)⟩

end S_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified (solution)
