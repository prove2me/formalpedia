-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1b94f626-ba1d-5c25-b6a7-6c080b6382e3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
import Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
import Theorems.Thm_CerednikDrinfeld_QM_exists_torsion_point_ne_one_of_two_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PDivisibleGroup.instHopfAlgebra"
p2m_attr_erase "instance" "PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem"
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one"
p2m_attr_erase "simp" "PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply"
p2m_attr_erase "simp" "TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace PosHelpers

open Opposite

theorem exists_unit_hom_ne_zero_of_section {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) (hs : s ≠ 0) :
    ∃ φ : 𝟙_ X.Modules ⟶ M, φ ≠ 0 := by
  let σ : M.val.sections := PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map (homOfLE (le_top (a := U.unop))).op s)
    (fun U V g => by
      show M.presheaf.map g (M.presheaf.map (homOfLE (le_top (a := U.unop))).op s) =
        M.presheaf.map (homOfLE (le_top (a := V.unop))).op s
      rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
      congr 1)
  refine ⟨M.unitHomEquiv.symm σ, fun h => hs ?_⟩
  have h1 := SheafOfModules.unitHomEquiv_apply_coe M (M.unitHomEquiv.symm σ) (op ⊤)
  rw [Equiv.apply_symm_apply, h] at h1

  have h2 : σ.val (op ⊤) = s := by
    show M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op s = s
    rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 (op ⊤) from Subsingleton.elim _ _, M.presheaf.map_id]
    rfl
  rw [← h2, h1]
  show ((0 : 𝟙_ X.Modules ⟶ M).app ⊤) (1 : Γ(X, ⊤)) = 0
  rw [Scheme.Modules.Hom.zero_app]
  rfl

theorem app_top_one_ne_zero {X : Scheme.{0}} {M : X.Modules} (φ : 𝟙_ X.Modules ⟶ M) (hφ : φ ≠ 0) :
    (φ.app ⊤) (1 : Γ(X, ⊤)) ≠ 0 := by
  intro h
  apply hφ
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  have hU : (1 : X.ringCatSheaf.val.obj U) =
      (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE (le_top (a := U.unop))).op (1 : X.ringCatSheaf.val.obj (op ⊤)) :=
    (PresheafOfModules.unit_map_one _ (homOfLE (le_top (a := U.unop))).op).symm
  have h' : (φ.val.app (op ⊤)) (1 : X.ringCatSheaf.val.obj (op ⊤)) = 0 := h
  have h'' : ((0 : 𝟙_ X.Modules ⟶ M).val.app (op ⊤)) (1 : X.ringCatSheaf.val.obj (op ⊤)) = 0 := by
    show ((0 : 𝟙_ X.Modules ⟶ M).app ⊤) _ = 0
    rw [Scheme.Modules.Hom.zero_app]; rfl
  rw [hU, PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  exact congrArg (fun y => (M.val.map (homOfLE (le_top (a := U.unop))).op) y) (h'.trans h''.symm)

end PosHelpers

namespace AlphaHelpers

open Opposite

theorem app_eq_zero_of_le {X : Scheme} {𝓛 : X.Modules} (s : 𝟙_ X.Modules ⟶ 𝓛) {U V : X.Opens} (hVU : V ≤ U)
    (r : Γ(X, U)) (hsr : s.app U r = 0) (hunit : IsUnit (X.presheaf.map (homOfLE hVU).op r)) : s.app V = 0 := by

  have h1 : (s.app V) (1 : Γ(X, V)) = 𝓛.presheaf.map (homOfLE hVU).op ((s.app U) (1 : Γ(X, U))) := by
    have hn := PresheafOfModules.naturality_apply s.val (homOfLE hVU).op (1 : Γ(X, U))
    have h1' : (𝟙_ X.Modules).val.map (homOfLE hVU).op (1 : Γ(X, U)) = (1 : Γ(X, V)) :=
      PresheafOfModules.unit_map_one _ _
    rw [h1'] at hn
    exact hn
  have hr1 : (s.app U) r = r • (s.app U) (1 : Γ(X, U)) := by
    rw [← Scheme.Modules.Hom.app_smul]
    exact congrArg (s.app U) (mul_one r).symm
  have h2 : X.presheaf.map (homOfLE hVU).op r • (s.app V) (1 : Γ(X, V)) = 0 := by
    rw [h1]
    show X.presheaf.map (homOfLE hVU).op r • 𝓛.presheaf.map (homOfLE hVU).op ((s.app U) (1 : Γ(X, U))) = 0
    rw [← Scheme.Modules.map_smul, ← hr1, hsr, map_zero]
  have h3 : (s.app V) (1 : Γ(X, V)) = 0 := by
    obtain ⟨w, hw⟩ := hunit
    rw [← hw] at h2
    have := congrArg (fun m => (↑w⁻¹ : Γ(X, V)) • m) h2
    simpa [← mul_smul, smul_zero] using this
  have key : ∀ y : Γ(X, V), (s.app V) y = 0 := by
    intro y
    have : (s.app V) y = y • (s.app V) (1 : Γ(X, V)) := by
      rw [← Scheme.Modules.Hom.app_smul]
      exact congrArg (s.app V) (mul_one y).symm
    rw [this, h3, smul_zero]
  ext y
  exact key y

theorem mono_of_ne_zero {X : Scheme} [IsIntegral X] {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (s : 𝟙_ X.Modules ⟶ 𝓛) (hs : s ≠ 0) : Mono s := by
  rw [Scheme.Modules.Hom.mono_iff_injective]
  intro U
  show ∀ a b : Γ(X, U), s.app U a = s.app U b → a = b
  intro a b hab
  by_contra hne
  apply hs
  have hr : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hsr : s.app U (a - b) = 0 := by
    have h := map_sub (ConcreteCategory.hom (s.app U)) a b
    exact h.trans (sub_eq_zero.mpr hab)

  have hUne : (U : Set X).Nonempty := by
    by_contra hU
    apply hr
    have hU' : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hU)
    have : Subsingleton Γ(X, U) := by
      rw [hU']; exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

  let D : X.Opens := X.basicOpen (a - b)
  have hξU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)
  have hξD : genericPoint X ∈ D := by
    rw [Scheme.mem_basicOpen _ _ _ hξU]
    have hne0 : (X.presheaf.germ U (genericPoint X) hξU) (a - b) ≠ 0 := by
      intro h0
      apply hr
      apply germ_injective_of_isIntegral X (genericPoint X) hξU
      rw [h0]
      exact (map_zero _).symm
    exact isUnit_iff_ne_zero.mpr hne0
  have hDne : (D : Set X).Nonempty := ⟨_, hξD⟩

  have hD : ∀ W : (D : Scheme).Opens, s.app (D.ι ''ᵁ W) = 0 := by
    intro W
    have hWD : D.ι ''ᵁ W ≤ D := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hWU : D.ι ''ᵁ W ≤ U := hWD.trans (X.basicOpen_le _)
    refine app_eq_zero_of_le s hWU (a - b) hsr ?_
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (a - b))).op (a - b)) := RingedSpace.isUnit_res_basicOpen _ (a - b)
    have := hu.map (X.presheaf.map (homOfLE hWD).op).hom
    rwa [← CategoryTheory.comp_apply, ← X.presheaf.map_comp] at this
  have hD' : (Scheme.Modules.restrictFunctor D.ι).map s = 0 := by
    apply Scheme.Modules.hom_ext
    intro W
    rw [Scheme.Modules.Hom.zero_app]
    exact hD W
  have hD'' : (Scheme.Modules.pullback D.ι).map s = 0 := by
    let e := Scheme.Modules.restrictFunctorIsoPullback D.ι
    have hn := e.hom.naturality s

    rw [hD', zero_comp] at hn
    rw [← cancel_epi (e.hom.app _), ← hn, comp_zero]
  exact Scheme.Modules.IsInvertible.hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral (Scheme.Modules.isInvertible_unit X) h𝓛 s D hDne hD''

end AlphaHelpers

namespace SignHelpers

theorem preservesMono_tensorLeft {X : Scheme.{0}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    (tensorLeft M).PreservesMonomorphisms := by
  obtain ⟨-, ⟨eM⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hM
  let e' : Scheme.Modules.dual M ⊗ M ≅ 𝟙_ X.Modules := β_ _ _ ≪≫ eM
  let tl : ∀ {P Q : X.Modules} (_ : P ≅ Q), tensorLeft P ≅ tensorLeft Q := fun i =>
    NatIso.ofComponents (fun Z => whiskerRightIso i Z) (fun f => by simp [whisker_exchange])
  let E : X.Modules ≌ X.Modules := CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft (Scheme.Modules.dual M))
    ((leftUnitorNatIso X.Modules).symm ≪≫ tl e'.symm ≪≫ tensorLeftTensor _ _)
    ((tensorLeftTensor _ _).symm ≪≫ tl eM ≪≫ leftUnitorNatIso X.Modules)
  exact Functor.preservesMonomorphisms_of_adjunction E.symm.toAdjunction

theorem mono_whiskerLeft {X : Scheme.{0}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    {P Q : X.Modules} (g : P ⟶ Q) [Mono g] : Mono (M ◁ g) := by
  haveI := preservesMono_tensorLeft hM
  exact (tensorLeft M).map_mono g

theorem exists_unit_hom_ne_zero_of_pos (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hpos : 0 < Scheme.Modules.geomFibreH0Finrank f M k (RingHom.id k)) :
    ∃ φ : 𝟙_ A.Modules ⟶ M, φ ≠ 0 := by
  rw [Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f M hM] at hpos
  have hnt : Nontrivial (Γ(M, ⊤) : Type) := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
    exact Module.nontrivial_of_finrank_pos hpos
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(M, ⊤))
  exact PosHelpers.exists_unit_hom_ne_zero_of_section M m hm

end SignHelpers

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) (hg : 1 ≤ g)
    (𝓛₀ 𝓛₁ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (h₁ : Scheme.Modules.IsInvertible 𝓛₁)
    (hK₀ : KernelTrivial f L 𝓛₀)
    (hpos₀ : 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₀ k (RingHom.id k))
    (hpos₁ : 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₁ k (RingHom.id k)) :
    ¬ ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        Nonempty ((Scheme.Modules.pullback (L.translate x)).obj (𝓛₁ ⊗ 𝓛₀) ≅ 𝓛₁ ⊗ 𝓛₀) := by
  intro hP

  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI hGI : GeometricallyIntegral f := hA.geometricallyIntegral
  haveI : IsIntegral A := GeometricallyIntegral.isIntegral_of_subsingleton f

  have hL0 : ¬ Nonempty (𝓛₀ ≅ 𝟙_ A.Modules) := by
    rintro ⟨e₀⟩
    obtain ⟨R, _, t, x, -, hx⟩ := CerednikDrinfeld.QM.exists_torsion_point_ne_one_of_two_le k f L hc hA g hdim hg 2 le_rfl
    apply hx
    apply hK₀ R t x
    rw [← isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit k f L 𝓛₀ h₀ R t x]
    have hu : L.IsInStabilizer (𝟙_ A.Modules) t x := L.isInStabilizer_unit t x
    exact (Scheme.Modules.LocallyIsoOver.of_iso _ ((Scheme.Modules.pullback (L.mulRight t x)).mapIso e₀)).trans
      (hu.trans (Scheme.Modules.LocallyIsoOver.of_iso _ ((Scheme.Modules.pullback (pullback.fst f t)).mapIso e₀.symm)))
  apply hL0

  obtain ⟨s₀, hs₀⟩ := SignHelpers.exists_unit_hom_ne_zero_of_pos k f 𝓛₀ h₀ hpos₀
  obtain ⟨s₁, hs₁⟩ := SignHelpers.exists_unit_hom_ne_zero_of_pos k f 𝓛₁ h₁ hpos₁
  haveI : Mono s₀ := AlphaHelpers.mono_of_ne_zero h₀ s₀ hs₀
  haveI : Mono s₁ := AlphaHelpers.mono_of_ne_zero h₁ s₁ hs₁
  have hid1 : 𝟙 (𝟙_ A.Modules) ≠ 0 := fun h => hs₀ (by rw [← Category.id_comp s₀, h, zero_comp])
  have hid0 : 𝟙 𝓛₀ ≠ 0 := fun h => hs₀ (by rw [← Category.comp_id s₀, h, comp_zero])

  have hPic : InPicZero f L (𝓛₁ ⊗ 𝓛₀) := ⟨h₁.tensor_monoidalV2 h₀, hP⟩
  by_cases hP1 : Nonempty (𝓛₁ ⊗ 𝓛₀ ≅ 𝟙_ A.Modules)
  ·
    obtain ⟨φ⟩ := hP1
    haveI : Mono (𝓛₀ ◁ s₁) := SignHelpers.mono_whiskerLeft h₀ s₁
    obtain ⟨t, ht_def⟩ : ∃ t : 𝓛₀ ⟶ 𝟙_ A.Modules, t = (ρ_ 𝓛₀).inv ≫ (𝓛₀ ◁ s₁) ≫ (β_ 𝓛₀ 𝓛₁).hom ≫ φ.hom :=
      ⟨_, rfl⟩
    haveI : Mono t := by rw [ht_def]; infer_instance
    have ht : t ≠ 0 := fun h => hid0 ((cancel_mono t).mp (by rw [h, comp_zero, comp_zero]))

    have hγ : t ≫ s₀ ≠ 0 := by
      intro h0; apply ht; rw [← cancel_mono s₀, h0, Limits.zero_comp]
    obtain ⟨u, hu⟩ := Scheme.Modules.IsInvertible.exists_forall_app_eq_smul h₀ (t ≫ s₀)
    have hu0 : u ≠ 0 := by
      intro h0; apply hγ
      apply Scheme.Modules.hom_ext; intro U; ext y
      rw [Scheme.Modules.Hom.zero_app, hu U y, h0, map_zero, zero_smul]; rfl
    have hbij := (geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth f).mp inferInstance
    have huU : IsUnit u := by
      obtain ⟨c, hc'⟩ := hbij.2 u
      have hc0 : c ≠ 0 := by rintro rfl; apply hu0; rw [← hc', map_zero]
      rw [← hc']
      exact (IsUnit.mk0 c hc0).map _
    obtain ⟨w, hw⟩ := huU
    haveI : IsIso (t ≫ s₀) := by
      rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
      intro U
      rw [ConcreteCategory.isIso_iff_bijective]
      constructor
      · intro a b hab
        rw [hu U a, hu U b, ← hw] at hab
        have := congrArg (fun z => A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (↑w⁻¹ : Γ(A, ⊤)) • z) hab
        simpa [← mul_smul, ← map_mul] using this
      · intro b
        refine ⟨A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (↑w⁻¹ : Γ(A, ⊤)) • b, ?_⟩
        rw [hu U, ← hw, ← mul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
    haveI : IsSplitEpi s₀ := IsSplitEpi.mk' ⟨inv (t ≫ s₀) ≫ t, by rw [Category.assoc, IsIso.inv_hom_id]⟩
    haveI : IsIso s₀ := isIso_of_mono_of_isSplitEpi s₀
    exact ⟨(asIso s₀).symm⟩
  ·
    exfalso
    haveI hsub := subsingleton_sections_of_inPicZero_of_not_iso_unit k f L hc hA (𝓛₁ ⊗ 𝓛₀) hPic hP1
    haveI : Mono (𝓛₁ ◁ s₀) := SignHelpers.mono_whiskerLeft h₁ s₀
    obtain ⟨σ, hσ_def⟩ : ∃ σ : 𝟙_ A.Modules ⟶ 𝓛₁ ⊗ 𝓛₀, σ = s₁ ≫ (ρ_ 𝓛₁).inv ≫ (𝓛₁ ◁ s₀) := ⟨_, rfl⟩
    haveI : Mono σ := by rw [hσ_def]; infer_instance
    have hσ : σ ≠ 0 := fun h => hid1 ((cancel_mono σ).mp (by rw [h, comp_zero, comp_zero]))
    exact PosHelpers.app_top_one_ne_zero σ hσ (Subsingleton.elim _ _)

end S_AlgebraicGeometry_Polarisation_not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos (solution)
