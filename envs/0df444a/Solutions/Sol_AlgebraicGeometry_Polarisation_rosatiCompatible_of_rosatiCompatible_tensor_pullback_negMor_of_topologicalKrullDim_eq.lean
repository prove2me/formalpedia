-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_topologicalKrullDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4e5759ae-7ec3-5bf1-86f4-501233d36f24

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_tensor_self_iso_unit_of_birigidified
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap
import Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_pullback_negMor_tensor_dual
import Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_iff_nonempty_mumfordBundle_iso_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_topologicalKrullDim_eq
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"

noncomputable section

namespace RosatiRoot

variable {V : Scheme.{0}}

def isoOfTensorIsoUnit (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _) (i' : X ⊗ Y' ≅ 𝟙_ _) : Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫ (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

def tensorTensorTensorComm (W X Y Z : V.Modules) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ _ _ _ ≪≫ (Iso.refl W ⊗ᵢ ((α_ _ _ _).symm ≪≫ (β_ X Y ⊗ᵢ Iso.refl Z) ≪≫ α_ _ _ _)) ≪≫ (α_ _ _ _).symm

theorem nonempty_dual_congr {L L' : V.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (e : L ≅ L') : Nonempty (Scheme.Modules.dual L ≅ Scheme.Modules.dual L') :=
  ⟨isoOfTensorIsoUnit L' _ _ ((e.symm ⊗ᵢ Iso.refl _) ≪≫ hL.dual_monoidalV2.2.some) hL'.dual_monoidalV2.2.some⟩

theorem nonempty_dual_unit_iso (V : Scheme.{0}) : Nonempty (Scheme.Modules.dual (𝟙_ V.Modules) ≅ 𝟙_ V.Modules) :=
  ⟨(λ_ _).symm ≪≫ (Scheme.Modules.isInvertible_unit V).dual_monoidalV2.2.some⟩

theorem nonempty_sq_iso_unit {X Y : V.Modules} (hY : Scheme.Modules.IsInvertible Y) (e : X ⊗ X ≅ Y ⊗ Y) :
    Nonempty ((X ⊗ Scheme.Modules.dual Y) ⊗ (X ⊗ Scheme.Modules.dual Y) ≅ 𝟙_ _) := by
  obtain ⟨j⟩ := hY.dual_monoidalV2.2
  exact ⟨tensorTensorTensorComm _ _ _ _ ≪≫ (e ⊗ᵢ Iso.refl _) ≪≫ tensorTensorTensorComm _ _ _ _ ≪≫ (j ⊗ᵢ j) ≪≫ λ_ _⟩

theorem nonempty_iso_of_tensor_dual_iso_unit {X Y : V.Modules} (hY : Scheme.Modules.IsInvertible Y)
    (e : X ⊗ Scheme.Modules.dual Y ≅ 𝟙_ _) : Nonempty (X ≅ Y) := by
  obtain ⟨j⟩ := hY.dual_monoidalV2.2
  exact ⟨isoOfTensorIsoUnit (Scheme.Modules.dual Y) X Y ((β_ _ _) ≪≫ e) ((β_ _ _) ≪≫ j)⟩

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

theorem isInvertible_mumfordBundle {𝓛 : A.Modules} (h : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) := by
  unfold mumfordBundle
  exact (h.pullback _).tensor_monoidalV2 ((h.dual_monoidalV2.1.pullback _).tensor_monoidalV2 (h.dual_monoidalV2.1.pullback _))

theorem nonempty_mumfordBundle_congr {𝓛 𝓛' : A.Modules} (h : Scheme.Modules.IsInvertible 𝓛) (h' : Scheme.Modules.IsInvertible 𝓛')
    (e : 𝓛 ≅ 𝓛') : Nonempty (mumfordBundle f L 𝓛 ≅ mumfordBundle f L 𝓛') := by
  obtain ⟨d⟩ := nonempty_dual_congr h h' e
  unfold mumfordBundle
  exact ⟨(Scheme.Modules.pullback _).mapIso e ⊗ᵢ ((Scheme.Modules.pullback _).mapIso d ⊗ᵢ (Scheme.Modules.pullback _).mapIso d)⟩

theorem pushPt_one {φ : A ⟶ A} (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) : pushPt φ hφ (L.one t) = L.one t := by
  have h := hhom t (L.one t) (L.one t)
  rw [L.mul_one] at h
  symm
  calc L.one t = L.mul t (L.inv t (pushPt φ hφ (L.one t))) (pushPt φ hφ (L.one t)) := (L.inv_mul_cancel t _).symm
    _ = L.mul t (L.inv t (pushPt φ hφ (L.one t))) (L.mul t (pushPt φ hφ (L.one t)) (pushPt φ hφ (L.one t))) :=
        congrArg (L.mul t (L.inv t (pushPt φ hφ (L.one t)))) h
    _ = L.mul t (L.mul t (L.inv t (pushPt φ hφ (L.one t))) (pushPt φ hφ (L.one t))) (pushPt φ hφ (L.one t)) :=
        (L.mul_assoc t _ _ _).symm
    _ = pushPt φ hφ (L.one t) := by rw [L.inv_mul_cancel, L.one_mul]

end RosatiRoot

open RosatiRoot in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act_hom : ∀ (x : I) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (star : I → I) (𝓛₁ : A.Modules) (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (hK : KernelTrivial f L 𝓛₁)
    (hR : RosatiCompatible f L (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₁) act act_over star) :
    RosatiCompatible f L 𝓛₁ act act_over star := by
  classical
  intro b
  rw [locIsoOnBase_iff_nonempty_iso_of_field]

  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₁) := h₁.pullback _
  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛₁) := isInvertible_mumfordBundle f L h₁

  let u : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)
  let v : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition)
  change Nonempty ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁) ≅ (Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁))
  have e0 : Nonempty ((Scheme.Modules.pullback u).obj (mumfordBundle f L (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₁)) ≅
      (Scheme.Modules.pullback v).obj (mumfordBundle f L (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₁))) :=
    (locIsoOnBase_iff_nonempty_iso_of_field _ _ _).1 (hR b)

  have hP : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₁ ⊗ Scheme.Modules.dual 𝓛₁) :=
    hN.tensor_monoidalV2 h₁.dual_monoidalV2.1
  have eΛP : Nonempty (mumfordBundle f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₁ ⊗ Scheme.Modules.dual 𝓛₁) ≅ 𝟙_ _) :=
    (inPicZero_iff_nonempty_mumfordBundle_iso_unit k f L hc hA _ hP).1
      (inPicZero_pullback_negMor_tensor_dual k f L hc hA 𝓛₁ h₁)
  have eNP : Nonempty ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₁ ≅
      ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₁ ⊗ Scheme.Modules.dual 𝓛₁) ⊗ 𝓛₁) := by
    obtain ⟨j⟩ := h₁.dual_monoidalV2.2
    exact ⟨(ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ ((β_ _ _) ≪≫ j).symm) ≪≫ (α_ _ _ _).symm⟩
  have eΛN : Nonempty (mumfordBundle f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₁) ≅ mumfordBundle f L 𝓛₁) := by
    obtain ⟨e1⟩ := nonempty_mumfordBundle_congr f L hN (hP.tensor_monoidalV2 h₁) eNP.some
    obtain ⟨e2⟩ := nonempty_mumfordBundle_tensor_iso_tensor k f L _ _ hP h₁
    obtain ⟨e3⟩ := eΛP
    exact ⟨e1 ≪≫ e2 ≪≫ (e3 ⊗ᵢ Iso.refl _) ≪≫ λ_ _⟩
  have eΛsym : Nonempty (mumfordBundle f L (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₁) ≅
      mumfordBundle f L 𝓛₁ ⊗ mumfordBundle f L 𝓛₁) := by
    obtain ⟨e1⟩ := nonempty_mumfordBundle_tensor_iso_tensor k f L _ _ h₁ hN
    obtain ⟨e2⟩ := eΛN
    exact ⟨e1 ≪≫ (Iso.refl _ ⊗ᵢ e2)⟩

  have hX : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁)) := hΛ.pullback _
  have hY : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁)) := hΛ.pullback _
  have eXY : Nonempty ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁) ⊗ (Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁) ≅
      (Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁) ⊗ (Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁)) := by
    obtain ⟨e⟩ := e0
    obtain ⟨es⟩ := eΛsym
    exact ⟨(Scheme.Modules.pullbackTensorObjIso u _ _).symm ≪≫ (Scheme.Modules.pullback u).mapIso es.symm ≪≫ e ≪≫
      (Scheme.Modules.pullback v).mapIso es ≪≫ Scheme.Modules.pullbackTensorObjIso v _ _⟩
  have hQ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁) ⊗
      Scheme.Modules.dual ((Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁))) := hX.tensor_monoidalV2 hY.dual_monoidalV2.1
  have hsq := nonempty_sq_iso_unit hY eXY.some

  let tk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k))
  let z : SchemeHomOver tk f := RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)
  have hz : z = L.one tk := RelativeGroupLaw.AlgPoints.toPoint_zero
  let s : pullback f tk ⟶ pullback f f := sliceAt f z
  have hact_one : ∀ c : I, z.1 ≫ act c = z.1 := fun c => by
    have := congrArg Subtype.val (pushPt_one f L (act_over c) (act_hom c) tk)
    rw [hz]; exact this
  obtain ⟨⟨hs1⟩, ⟨hs2⟩⟩ := nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap k f L hc 𝓛₁ h₁

  let w : I → (pullback f tk ⟶ pullback f tk) := fun c =>
    pullback.lift (pullback.fst f tk ≫ act c) (pullback.snd f tk) (by rw [Category.assoc, act_over]; exact pullback.condition)
  have id1 : s ≫ u = s := by
    apply pullback.hom_ext
    · simp only [s, u, sliceAt, Category.assoc, pullback.lift_fst]
    · simp only [s, u, sliceAt, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hact_one]
  have id2 : s ≫ v = w (star b) ≫ s := by
    apply pullback.hom_ext
    · simp only [s, v, w, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [s, v, w, sliceAt, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have id3 : s ≫ (pullbackSymmetry f f).hom ≫ u = w b ≫ s ≫ (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext
    · simp only [s, u, w, sliceAt, Category.assoc, pullback.lift_fst, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_fst_assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
    · simp only [s, u, w, sliceAt, Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
  have id4 : s ≫ (pullbackSymmetry f f).hom ≫ v = s ≫ (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext
    · simp only [s, v, sliceAt, Category.assoc, pullback.lift_fst, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_fst_assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, hact_one]
    · simp only [s, v, sliceAt, Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_fst]

  have eX1 : Nonempty ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁)) ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullbackComp s u).app _ ≪≫ (Scheme.Modules.pullbackCongr id1).app _ ≪≫ hs1⟩
  have eY1 : Nonempty ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁)) ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullbackComp s v).app _ ≪≫ (Scheme.Modules.pullbackCongr id2).app _ ≪≫
      ((Scheme.Modules.pullbackComp (w (star b)) s).app _).symm ≪≫ (Scheme.Modules.pullback (w (star b))).mapIso hs1 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (w (star b))⟩
  have eX2 : Nonempty ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj
      ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁))) ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullback s).mapIso ((Scheme.Modules.pullbackComp (pullbackSymmetry f f).hom u).app _) ≪≫
      (Scheme.Modules.pullbackComp s ((pullbackSymmetry f f).hom ≫ u)).app _ ≪≫
      (Scheme.Modules.pullbackCongr id3).app _ ≪≫
      ((Scheme.Modules.pullbackComp (w b) (s ≫ (pullbackSymmetry f f).hom)).app _).symm ≪≫
      (Scheme.Modules.pullback (w b)).mapIso (((Scheme.Modules.pullbackComp s (pullbackSymmetry f f).hom).app _).symm ≪≫ hs2) ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (w b)⟩
  have eY2 : Nonempty ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj
      ((Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁))) ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullback s).mapIso ((Scheme.Modules.pullbackComp (pullbackSymmetry f f).hom v).app _) ≪≫
      (Scheme.Modules.pullbackComp s ((pullbackSymmetry f f).hom ≫ v)).app _ ≪≫
      (Scheme.Modules.pullbackCongr id4).app _ ≪≫
      ((Scheme.Modules.pullbackComp s (pullbackSymmetry f f).hom).app _).symm ≪≫ hs2⟩

  have hQ1 : Nonempty ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁) ⊗
      Scheme.Modules.dual ((Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁))) ≅ 𝟙_ _) := by
    obtain ⟨ex⟩ := eX1
    obtain ⟨ey⟩ := eY1
    obtain ⟨pd⟩ := hY.pullback_dual_monoidalV2 s
    obtain ⟨dy⟩ := nonempty_dual_congr (hY.pullback s) (Scheme.Modules.isInvertible_unit _) ey
    obtain ⟨du⟩ := nonempty_dual_unit_iso (pullback f tk)
    exact ⟨Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫ (ex ⊗ᵢ (pd ≪≫ dy ≪≫ du)) ≪≫ λ_ _⟩
  have hQ2 : Nonempty ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj
      ((Scheme.Modules.pullback u).obj (mumfordBundle f L 𝓛₁) ⊗
        Scheme.Modules.dual ((Scheme.Modules.pullback v).obj (mumfordBundle f L 𝓛₁)))) ≅ 𝟙_ _) := by
    obtain ⟨ex⟩ := eX2
    obtain ⟨ey⟩ := eY2
    obtain ⟨pd1⟩ := hY.pullback_dual_monoidalV2 (pullbackSymmetry f f).hom
    obtain ⟨pd2⟩ := (hY.pullback (pullbackSymmetry f f).hom).pullback_dual_monoidalV2 s
    obtain ⟨dy⟩ := nonempty_dual_congr ((hY.pullback _).pullback s) (Scheme.Modules.isInvertible_unit _) ey
    obtain ⟨du⟩ := nonempty_dual_unit_iso (pullback f tk)
    exact ⟨(Scheme.Modules.pullback s).mapIso (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ pd1)) ≪≫
      Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫ (ex ⊗ᵢ (pd2 ≪≫ dy ≪≫ du)) ≪≫ λ_ _⟩

  have hQtriv := nonempty_iso_unit_of_tensor_self_iso_unit_of_birigidified k f L hc hA g hdim _ hQ hQ1 hQ2 hsq
  exact nonempty_iso_of_tensor_dual_iso_unit hY hQtriv.some

end

end S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_topologicalKrullDim_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_tensor_pullback_negMor_of_topologicalKrullDim_eq (solution)
