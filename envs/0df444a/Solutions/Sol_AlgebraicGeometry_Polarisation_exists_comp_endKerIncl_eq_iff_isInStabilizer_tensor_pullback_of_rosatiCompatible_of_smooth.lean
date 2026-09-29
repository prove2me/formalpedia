-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cf6baab8-505e-51bf-9406-16af715ecb2e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation CerednikDrinfeld.QM"

namespace RosatiPhiSquareT29

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))

noncomputable def fstSlice (x : SchemeHomOver t f) : pullback f t ⟶ pullback f f :=
  pullback.lift (pullback.snd f t ≫ x.1) (pullback.fst f t)
    (by rw [Category.assoc, x.2]; exact pullback.condition.symm)

@[scoped simp] theorem fstSlice_fst (x : SchemeHomOver t f) : fstSlice f t x ≫ pullback.fst f f = pullback.snd f t ≫ x.1 :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem fstSlice_snd (x : SchemeHomOver t f) : fstSlice f t x ≫ pullback.snd f f = pullback.fst f t :=
  pullback.lift_snd _ _ _

noncomputable def toTriple (x x' : SchemeHomOver t f) : pullback f t ⟶ pullback (pullback.fst f f ≫ f) f :=
  pullback.lift
    (pullback.lift (pullback.snd f t ≫ x.1) (pullback.snd f t ≫ x'.1)
      (by rw [Category.assoc, x.2, Category.assoc, x'.2]))
    (pullback.fst f t)
    (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, x.2]; exact pullback.condition.symm)

theorem lift_addMor {Y : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver s f) :
    pullback.lift u.1 v.1 (by rw [u.2, v.2]) ≫ addMor f L = (L.mul s u v).1 := by
  have hψ : pullback.lift u.1 v.1 (by rw [u.2, v.2]) ≫ (pullback.fst f f ≫ f) = s := by
    rw [← Category.assoc, pullback.lift_fst]; exact u.2
  have nat := L.mul_natural (pullback.fst f f ≫ f) s (pullback.lift u.1 v.1 (by rw [u.2, v.2])) hψ
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have hP : schemeHomOverComp (pullback.lift u.1 v.1 (by rw [u.2, v.2])) hψ ⟨pullback.fst f f, rfl⟩ = u :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have hQ : schemeHomOverComp (pullback.lift u.1 v.1 (by rw [u.2, v.2])) hψ
      ⟨pullback.snd f f, pullback.condition.symm⟩ = v :=
    Subtype.ext (pullback.lift_snd _ _ _)
  rw [hP, hQ] at nat
  exact congrArg Subtype.val nat

theorem toTriple_addMorProd (x x' : SchemeHomOver t f) :
    toTriple f t x x' ≫
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ addMor f L) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, addMor_over]; exact pullback.condition) =
      fstSlice f t (L.mul t x x') := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, fstSlice_fst, ← Category.assoc, toTriple, pullback.lift_fst]

    have h := lift_addMor f L (pullback.snd f t ≫ t) (schemeHomOverComp (pullback.snd f t) rfl x)
      (schemeHomOverComp (pullback.snd f t) rfl x')
    have nat := L.mul_natural t (pullback.snd f t ≫ t) (pullback.snd f t) rfl x x'
    rw [← nat] at h
    exact h
  · rw [Category.assoc, pullback.lift_snd, fstSlice_snd, toTriple, pullback.lift_snd]

theorem toTriple_fst13 (x x' : SchemeHomOver t f) :
    toTriple f t x x' ≫
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc]; exact pullback.condition) =
      fstSlice f t x := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, fstSlice_fst, ← Category.assoc, toTriple, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, fstSlice_snd, toTriple, pullback.lift_snd]

theorem toTriple_snd23 (x x' : SchemeHomOver t f) :
    toTriple f t x x' ≫
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) =
      fstSlice f t x' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, fstSlice_fst, ← Category.assoc, toTriple, pullback.lift_fst, pullback.lift_snd]
  · rw [Category.assoc, pullback.lift_snd, fstSlice_snd, toTriple, pullback.lift_snd]

noncomputable def compIso {X Y Z : Scheme.{0}} {p : X ⟶ Y} {q : Y ⟶ Z} {r : X ⟶ Z} (h : p ≫ q = r) (M : Z.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M) ≅ (Scheme.Modules.pullback r).obj M :=
  (Scheme.Modules.pullbackComp p q).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

theorem nonempty_pullback_fstSlice_mul_iso_tensor [IsAlgClosed k]
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (x x' : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (fstSlice f t (L.mul t x x'))).obj 𝓟 ≅
      (Scheme.Modules.pullback (fstSlice f t x)).obj 𝓟 ⊗ (Scheme.Modules.pullback (fstSlice f t x')).obj 𝓟) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Polarisation.nonempty_pullback_addMorProd_iso_tensor_of_birigidified k f L hc hA g hdim 𝓟 h𝓟 h₁ h₂
  exact ⟨(compIso (toTriple_addMorProd f L t x x') 𝓟).symm ≪≫ (Scheme.Modules.pullback (toTriple f t x x')).mapIso e ≪≫
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (compIso (toTriple_fst13 f t x x') 𝓟 ⊗ᵢ compIso (toTriple_snd23 f t x x') 𝓟)⟩

end RosatiPhiSquareT29
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

namespace RosatiPhiMSlice29

open RosatiPhiSquareT29

section Kit

variable {X Y : Scheme.{0}}

noncomputable def tensorPowCongr {L L' : X.Modules} (e : L ≅ L') : ∀ n : ℕ, L.tensorPow n ≅ L'.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => tensorPowCongr e n ⊗ᵢ e

noncomputable def mapTensorPow (F : Y.Modules ⥤ X.Modules) [F.Monoidal] (L : Y.Modules) :
    ∀ n : ℕ, F.obj (L.tensorPow n) ≅ (F.obj L).tensorPow n
  | 0 => (Functor.Monoidal.εIso F).symm
  | n + 1 => (Functor.Monoidal.μIso F (L.tensorPow n) L).symm ≪≫ (mapTensorPow F L n ⊗ᵢ Iso.refl _)

noncomputable def dualCongr {N N' : X.Modules} (e : N ≅ N') : Scheme.Modules.dual N ≅ Scheme.Modules.dual N' :=
  ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm

theorem nonempty_iso_unit_of_iso_tensor_self {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (e : M ≅ M ⊗ M) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  obtain ⟨d⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hM).2

  exact ⟨(ρ_ M).symm ≪≫ (Iso.refl M ⊗ᵢ d.symm) ≪≫ (α_ M M _).symm ≪≫ (e.symm ⊗ᵢ Iso.refl _) ≪≫ d⟩

end Kit
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

section Lambda

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

noncomputable def mumfordCongr {N N' : A.Modules} (e : N ≅ N') : mumfordBundle f L N ≅ mumfordBundle f L N' := by
  unfold mumfordBundle
  exact (Scheme.Modules.pullback (addMor f L)).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback (pullback.fst f f)).mapIso (dualCongr e) ⊗ᵢ
      (Scheme.Modules.pullback (pullback.snd f f)).mapIso (dualCongr e))

theorem nonempty_mumfordBundle_unit_iso : Nonempty (mumfordBundle f L (𝟙_ A.Modules) ≅ 𝟙_ (pullback f f).Modules) := by
  obtain ⟨e⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.isInvertible_unit A)).2
  let d : Scheme.Modules.dual (𝟙_ A.Modules) ≅ 𝟙_ A.Modules := (λ_ _).symm ≪≫ e
  exact ⟨(Scheme.Modules.pullbackTensorUnitObjIso (addMor f L) ⊗ᵢ
      (((Scheme.Modules.pullback (pullback.fst f f)).mapIso d ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ⊗ᵢ
       ((Scheme.Modules.pullback (pullback.snd f f)).mapIso d ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _))) ≪≫
    (Iso.refl _ ⊗ᵢ λ_ _) ≪≫ λ_ _⟩

theorem nonempty_mumfordBundle_tensorPow_iso {N : A.Modules} (hN : Scheme.Modules.IsInvertible N) :
    ∀ m : ℕ, Nonempty (mumfordBundle f L (N.tensorPow m) ≅ (mumfordBundle f L N).tensorPow m)
  | 0 => nonempty_mumfordBundle_unit_iso f L
  | m + 1 => by
    obtain ⟨e⟩ := nonempty_mumfordBundle_tensorPow_iso hN m
    obtain ⟨t⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle f L
      (N.tensorPow m) N (Scheme.Modules.IsInvertible.tensorPow_monoidalV2 hN m) hN
    exact ⟨t ≪≫ (e ⊗ᵢ Iso.refl _)⟩

end Lambda
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

section Main

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))

noncomputable abbrev timesOne (α : A ⟶ A) (hα : α ≫ f = f) : pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.fst f f ≫ α) (pullback.snd f f) (by rw [Category.assoc, hα]; exact pullback.condition)

noncomputable abbrev oneTimes (β : A ⟶ A) (hβ : β ≫ f = f) : pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.fst f f) (pullback.snd f f ≫ β) (by rw [Category.assoc, hβ]; exact pullback.condition)

theorem map_eq_timesOne_oneTimes (α : A ⟶ A) (hα : α ≫ f = f) :
    pullback.map f f f f α α (𝟙 _) (by rw [Category.comp_id, hα]) (by rw [Category.comp_id, hα]) =
      timesOne f α hα ≫ oneTimes f α hα := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

theorem timesOne_timesOne (α β : A ⟶ A) (hα : α ≫ f = f) (hβ : β ≫ f = f) :
    timesOne f α hα ≫ timesOne f β hβ = timesOne f (α ≫ β) (by rw [Category.assoc, hβ, hα]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

theorem fstSlice_timesOne (x : SchemeHomOver t f) (α : A ⟶ A) (hα : α ≫ f = f) :
    fstSlice f t x ≫ timesOne f α hα = fstSlice f t (pushPt α hα x) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, fstSlice_fst, fstSlice_fst, Category.assoc]; rfl
  · rw [Category.assoc, pullback.lift_snd, fstSlice_snd, fstSlice_snd]

theorem nsmul_mul (hc : L.IsCommutative) (x y : SchemeHomOver t f) :
    ∀ m : ℕ, L.nsmul t m (L.mul t x y) = L.mul t (L.nsmul t m x) (L.nsmul t m y)
  | 0 => by rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, L.mul_one]
  | m + 1 => by
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, nsmul_mul hc x y m,
      L.mul_assoc, L.mul_assoc, ← L.mul_assoc t (L.nsmul t m y) x y, hc t (L.nsmul t m y) x, L.mul_assoc]

theorem nonempty_pullback_fstSlice_nsmul_iso_tensorPow [IsAlgClosed k]
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (y : SchemeHomOver t f) :
    ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback (fstSlice f t (L.nsmul t n y))).obj 𝓟 ≅
      ((Scheme.Modules.pullback (fstSlice f t y)).obj 𝓟).tensorPow n)
  | 0 => by

    rw [RelativeGroupLaw.nsmul_zero]
    obtain ⟨e⟩ := nonempty_pullback_fstSlice_mul_iso_tensor f L t hc hA g hdim 𝓟 h𝓟 h₁ h₂ (L.one t) (L.one t)
    rw [L.mul_one] at e
    exact nonempty_iso_unit_of_iso_tensor_self (Scheme.Modules.IsInvertible.pullback _ h𝓟) e
  | n + 1 => by
    obtain ⟨ih⟩ := nonempty_pullback_fstSlice_nsmul_iso_tensorPow hc hA g hdim 𝓟 h𝓟 h₁ h₂ y n
    rw [RelativeGroupLaw.nsmul_succ]
    obtain ⟨e⟩ := nonempty_pullback_fstSlice_mul_iso_tensor f L t hc hA g hdim 𝓟 h𝓟 h₁ h₂ (L.nsmul t n y) y
    exact ⟨e ≪≫ (ih ⊗ᵢ Iso.refl _)⟩

private theorem _root_.RosatiPhiSquareT29.nonempty_pullback_fstSlice_mumfordBundle_tensor_pullback_iso [IsAlgClosed k]
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓛 polE : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hpolE : Scheme.Modules.IsInvertible polE)
    (n : ℕ) (e𝓛 : 𝓛 ≅ Scheme.Modules.tensorPow polE n)
    {I : Type} (ι : I → (A ⟶ A)) (hι : ∀ b : I, ι b ≫ f = f)
    (hιhom : ∀ (b : I) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ι b) (hι b) (L.mul t P Q) = L.mul t (pushPt (ι b) (hι b) P) (pushPt (ι b) (hι b) Q))
    (star : I → I) (b : I)
    (eRos : (Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ ι b)
        (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L polE) ≅
      (Scheme.Modules.pullback (pullback.lift (pullback.fst f f ≫ ι (star b)) (pullback.snd f f)
        (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L polE))
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        (mumfordBundle f L polE) ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L polE)) ≅ 𝟙_ _))
    (x : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (fstSlice f t x)).obj
        (mumfordBundle f L (𝓛 ⊗ (Scheme.Modules.pullback (ι b)).obj 𝓛)) ≅
      (Scheme.Modules.pullback
        (fstSlice f t (L.nsmul t n (L.mul t x (pushPt (ι (star b)) (hι (star b)) (pushPt (ι b) (hι b) x)))))).obj
          (mumfordBundle f L polE)) := by

  have hιb : ι b ≫ f = f := hι b
  have hιbs : ι (star b) ≫ f = f := hι (star b)
  set 𝓟 := mumfordBundle f L polE with h𝓟def
  have h𝓟 : Scheme.Modules.IsInvertible 𝓟 := by
    rw [h𝓟def]; unfold mumfordBundle
    exact Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ hpolE)
      (Scheme.Modules.IsInvertible.tensor_monoidalV2
        (Scheme.Modules.IsInvertible.pullback _ (Scheme.Modules.IsInvertible.dual_monoidalV2 hpolE).1)
        (Scheme.Modules.IsInvertible.pullback _ (Scheme.Modules.IsInvertible.dual_monoidalV2 hpolE).1))
  have hIb𝓛 : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (ι b)).obj 𝓛) := Scheme.Modules.IsInvertible.pullback _ h𝓛

  obtain ⟨eT⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle f L 𝓛 _ h𝓛 hIb𝓛

  obtain ⟨ePow⟩ := nonempty_mumfordBundle_tensorPow_iso f L hpolE n
  have eΛ𝓛 : mumfordBundle f L 𝓛 ≅ 𝓟.tensorPow n := mumfordCongr f L e𝓛 ≪≫ ePow

  obtain ⟨eH⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle f L (ι b) hιb
    (hιhom b) 𝓛 h𝓛

  have eSq : (Scheme.Modules.pullback (pullback.map f f f f (ι b) (ι b) (𝟙 _) (by rw [Category.comp_id, hιb])
      (by rw [Category.comp_id, hιb]))).obj 𝓟 ≅
      (Scheme.Modules.pullback (timesOne f ((ι b) ≫ (ι (star b))) (by rw [Category.assoc, hιbs, hιb]))).obj 𝓟 :=
    (Scheme.Modules.pullbackCongr (map_eq_timesOne_oneTimes f (ι b) hιb)).app 𝓟 ≪≫
      ((Scheme.Modules.pullbackComp _ _).app 𝓟).symm ≪≫
      (Scheme.Modules.pullback (timesOne f (ι b) hιb)).mapIso eRos ≪≫
      (Scheme.Modules.pullbackComp _ _).app 𝓟 ≪≫
      (Scheme.Modules.pullbackCongr (timesOne_timesOne f (ι b) (ι (star b)) hιb hιbs)).app 𝓟

  have eΛιb : mumfordBundle f L ((Scheme.Modules.pullback (ι b)).obj 𝓛) ≅
      ((Scheme.Modules.pullback (timesOne f ((ι b) ≫ (ι (star b))) (by rw [Category.assoc, hιbs, hιb]))).obj 𝓟).tensorPow n :=
    eH ≪≫ (Scheme.Modules.pullback _).mapIso eΛ𝓛 ≪≫ mapTensorPow _ 𝓟 n ≪≫ tensorPowCongr eSq n

  set c := pushPt (ι (star b)) hιbs (pushPt (ι b) hιb x) with hcdef
  have hcx : pushPt ((ι b) ≫ (ι (star b))) (by rw [Category.assoc, hιbs, hιb]) x = c := Subtype.ext (Category.assoc _ _ _).symm
  obtain ⟨ex⟩ := nonempty_pullback_fstSlice_nsmul_iso_tensorPow f L t hc hA g hdim 𝓟 h𝓟 h₁ h₂ x n
  obtain ⟨ec⟩ := nonempty_pullback_fstSlice_nsmul_iso_tensorPow f L t hc hA g hdim 𝓟 h𝓟 h₁ h₂ c n
  obtain ⟨emul⟩ := nonempty_pullback_fstSlice_mul_iso_tensor f L t hc hA g hdim 𝓟 h𝓟 h₁ h₂
    (L.nsmul t n x) (L.nsmul t n c)

  have eSl : (Scheme.Modules.pullback (fstSlice f t x)).obj
      ((Scheme.Modules.pullback (timesOne f ((ι b) ≫ (ι (star b))) (by rw [Category.assoc, hιbs, hιb]))).obj 𝓟) ≅
      (Scheme.Modules.pullback (fstSlice f t c)).obj 𝓟 :=
    compIso (fstSlice_timesOne f t x ((ι b) ≫ (ι (star b))) (by rw [Category.assoc, hιbs, hιb])) 𝓟 ≪≫
      (Scheme.Modules.pullbackCongr (congrArg (fstSlice f t) hcx)).app 𝓟

  have hn : L.nsmul t n (L.mul t x c) = L.mul t (L.nsmul t n x) (L.nsmul t n c) := nsmul_mul f L t hc x c n
  refine ⟨(Scheme.Modules.pullback (fstSlice f t x)).mapIso (eT ≪≫ (eΛ𝓛 ⊗ᵢ eΛιb)) ≪≫
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    ((mapTensorPow _ 𝓟 n ≪≫ ex.symm) ⊗ᵢ (mapTensorPow _ _ n ≪≫ tensorPowCongr eSl n ≪≫ ec.symm)) ≪≫
    emul.symm ≪≫ (Scheme.Modules.pullbackCongr (congrArg (fstSlice f t) hn.symm)).app 𝓟⟩

p2m_alias "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29.nonempty_pullback_fstSlice_mumfordBundle_tensor_pullback_iso" "RosatiPhiSquareT29.nonempty_pullback_fstSlice_mumfordBundle_tensor_pullback_iso"
end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

end RosatiPhiMSlice29
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

p2m_open "RosatiPhiSquareT29 P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

namespace RosatiPhiComp10

universe u

section General
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

theorem exists_comp_endKerι_eq_iff (γ : A ⟶ A) (hγ : γ ≫ f = f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (∃ x₀ : T ⟶ L.endKer ⟨γ, hγ⟩, x₀ ≫ L.endKerι ⟨γ, hγ⟩ = x.1) ↔ pushPt γ hγ x = L.one t := by
  constructor
  · rintro ⟨x₀, hx₀⟩
    apply Subtype.ext
    rw [mapPt_coe, one_coe, ← hx₀, Category.assoc]
    have hsnd : x₀ ≫ L.endKerStr ⟨γ, hγ⟩ = t := by
      rw [← L.endKerι_comp_base, ← Category.assoc, hx₀, x.2]
    rw [show L.endKerι ⟨γ, hγ⟩ ≫ γ = L.endKerStr ⟨γ, hγ⟩ ≫ (L.one (𝟙 _)).1 from L.endKerι_comp ⟨γ, hγ⟩,
      ← Category.assoc, hsnd]
  · intro h
    have h1 : x.1 ≫ γ = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
      rw [← one_coe, ← mapPt_coe γ hγ x]; exact congrArg Subtype.val h
    exact ⟨pullback.lift x.1 t h1, pullback.lift_fst _ _ _⟩

theorem nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointGroup t
    L.nsmul t n x = x ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ih]; rfl

theorem nsmul_two_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t (2 * n) x = L.mul t (L.nsmul t n x) (L.nsmul t n x) := by
  letI := L.pointGroup t
  rw [nsmul_eq_pow, nsmul_eq_pow, two_mul, pow_add]; rfl

end General
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

section Slices
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))

theorem sliceAt_comp_pullbackSymmetry (x : SchemeHomOver t f) :
    sliceAt f x ≫ (pullbackSymmetry f f).hom = fstSlice f t x := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, sliceAt, pullback.lift_snd, fstSlice, pullback.lift_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, sliceAt, pullback.lift_fst, fstSlice, pullback.lift_snd]

theorem nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fstSlice (hc : L.IsCommutative) (𝓜 : A.Modules)
    (x : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓜) ≅
      (Scheme.Modules.pullback (fstSlice f t x)).obj (mumfordBundle f L 𝓜)) := by
  obtain ⟨e⟩ := nonempty_pullback_pullbackSymmetry_mumfordBundle_iso k f L hc 𝓜
  exact ⟨((Scheme.Modules.pullback (sliceAt f x)).mapIso e).symm ≪≫ compIso (sliceAt_comp_pullbackSymmetry f t x) _⟩

theorem locIsoOnBase_congr_left {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M M'' : X.Modules} (e : M ≅ M'') (M' : X.Modules) :
    LocIsoOnBase g M M' ↔ LocIsoOnBase g M'' M' := by
  constructor
  · intro h s
    obtain ⟨U, hs, ⟨i⟩⟩ := h s
    exact ⟨U, hs, ⟨((Scheme.Modules.pullback _).mapIso e).symm ≪≫ i⟩⟩
  · intro h s
    obtain ⟨U, hs, ⟨i⟩⟩ := h s
    exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ i⟩⟩

end Slices
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

end RosatiPhiComp10
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.RosatiPhiSquareT29"

open RosatiPhiComp10 in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝓛 polE : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hpolE : Scheme.Modules.IsInvertible polE)
    (n : ℕ) (hn : LocIsoOnBase f 𝓛 (Scheme.Modules.tensorPow polE n))
    (hsym : IsSymmetric f L polE) (hK2 : KernelIsTwoTorsion f L polE)
    {I : Type} (ι : I → (A ⟶ A)) (hι : ∀ b : I, ι b ≫ f = f)
    (hιhom : ∀ (b : I) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (ι b) (hι b) (L.mul t P Q) = L.mul t (pushPt (ι b) (hι b) P) (pushPt (ι b) (hι b) Q))
    (star : I → I) (hRos : RosatiCompatible f L polE ι hι star)
    (b : I) (γ : A ⟶ A) (hγ : γ ≫ f = f)
    (hγpt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      pushPt γ hγ x = L.nsmul t (2 * n) (L.mul t x (pushPt (ι (star b)) (hι (star b)) (pushPt (ι b) (hι b) x)))) :
    ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ L.endKer ⟨γ, hγ⟩, x₀ ≫ L.endKerι ⟨γ, hγ⟩ = x.1) ↔
        L.IsInStabilizer (𝓛 ⊗ (Scheme.Modules.pullback (ι b)).obj 𝓛) t x := by
  intro R _ t x

  have hdim : ∀ s : ↥(Spec (CommRingCat.of K)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g := fun s =>
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq f g s
      ⟨(L.one (𝟙 _)).1.base s, by
        rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, (L.one (𝟙 _)).2]; rfl⟩

  obtain ⟨e𝓛⟩ := (locIsoOnBase_iff_nonempty_iso_of_field f 𝓛 (Scheme.Modules.tensorPow polE n)).1 hn
  obtain ⟨eRos⟩ := (locIsoOnBase_iff_nonempty_iso_of_field (pullback.fst f f ≫ f) _ _).1 (hRos b)

  obtain ⟨h₁, h₂⟩ := nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap K f L hc polE hpolE

  obtain ⟨eM⟩ := RosatiPhiSquareT29.nonempty_pullback_fstSlice_mumfordBundle_tensor_pullback_iso f L t hc hA g hdim
    𝓛 polE h𝓛 hpolE n e𝓛 ι hι hιhom star b eRos h₁ h₂ x

  obtain ⟨eX⟩ := nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fstSlice f L t hc
    (𝓛 ⊗ (Scheme.Modules.pullback (ι b)).obj 𝓛) x
  obtain ⟨eY⟩ := nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fstSlice f L t hc polE
    (L.nsmul t n (L.mul t x (pushPt (ι (star b)) (hι (star b)) (pushPt (ι b) (hι b) x))))
  have hM : Scheme.Modules.IsInvertible (𝓛 ⊗ (Scheme.Modules.pullback (ι b)).obj 𝓛) :=
    Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓛 (h𝓛.pullback (ι b))

  rw [isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit K f L _ hM R t x,
    locIsoOnBase_congr_left (pullback.snd f t) (eX ≪≫ eM ≪≫ eY.symm),
    hK2 R t, exists_comp_endKerι_eq_iff L γ hγ t x, hγpt t x, nsmul_two_mul]

end S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth (solution)
