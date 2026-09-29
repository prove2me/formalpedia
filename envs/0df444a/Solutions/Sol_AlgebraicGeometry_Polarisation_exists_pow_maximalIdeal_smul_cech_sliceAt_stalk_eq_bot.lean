-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e2effb0e-a5de-51bb-a555-f49981fd630c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
import Theorems.Thm_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime
import Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_localizedModule_cech_comap_of_not_mem_range_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace StalkTorsionAux

theorem smul_top_eq_bot_of_linearEquiv {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (e : M ≃ₗ[R] M') (h : I • (⊤ : Submodule R M') = ⊥) :
    I • (⊤ : Submodule R M) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha m _
  rw [Submodule.mem_bot]
  apply e.injective
  rw [map_smul, map_zero]
  have : a • e m ∈ I • (⊤ : Submodule R M') := Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [h, Submodule.mem_bot] at this

theorem smul_top_eq_bot_of_subsingleton {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    [Subsingleton M] (I : Ideal R) : I • (⊤ : Submodule R M) = ⊥ := by
  rw [show (⊤ : Submodule R M) = ⊥ from Subsingleton.elim _ _, Submodule.smul_bot]

theorem pow_smul_top_eq_bot_mono {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    (I : Ideal R) {m n : ℕ} (hmn : m ≤ n) (h : I ^ m • (⊤ : Submodule R M) = ⊥) :
    I ^ n • (⊤ : Submodule R M) = ⊥ :=
  le_bot_iff.mp ((Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)).trans h.le)

theorem subsingleton_HSucc_of_card_lt {R : Type} [CommRing R] {X : Scheme.{0}} {π : X ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (𝒰 : X.OrderedAffineCover) (i : ℕ) (h : Fintype.card 𝒰.ι < i + 2) :
    Subsingleton (F.HSucc 𝒰 i) := by
  haveI : IsEmpty (𝒰.Idx (i + 1)) := ⟨fun s => by
    have := Fintype.card_le_of_injective s.1 s.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  haveI : Subsingleton (F.cochain 𝒰 (i + 1)) := inferInstance
  haveI : Subsingleton (LinearMap.ker (F.d 𝒰 (i + 1))) := inferInstance
  infer_instance

end StalkTorsionAux

theorem isNoetherianRing_sections_of_isAffineOpen
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (V : A.Opens) (hV : IsAffineOpen V) : IsNoetherianRing Γ(A, V) := by
  letI algK : Algebra K Γ(A, V) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI hFT : Algebra.FiniteType K Γ(A, V) := by
    have h1 : RingHom.FiniteType (f.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
      ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv
    have h2 : ((f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).FiniteType :=
      h1.comp (RingHom.FiniteType.of_surjective _ hbij.surjective)
    exact h2
  exact Algebra.FiniteType.isNoetherianRing K Γ(A, V)

theorem torsion_of_offKappa
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) (V : A.Opens) (hV : IsAffineOpen V) (hyV : y ∈ V)
    (H : Type) [AddCommGroup H] [Module Γ(A, V) H] [Module.Finite Γ(A, V) H]
    (hH : ∀ 𝔪 : MaximalSpectrum Γ(A, V), hV.fromSpec.base 𝔪.toPrimeSpectrum ∉ Set.range κ.base →
      Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    letI algR : Algebra Γ(A, V) (A.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
    ∃ n : ℕ, IsLocalRing.maximalIdeal (A.presheaf.stalk y) ^ n •
      (⊤ : Submodule (A.presheaf.stalk y) (TensorProduct Γ(A, V) (A.presheaf.stalk y) H)) = ⊥ := by
  classical
  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  letI algR : Algebra Γ(A, V) (A.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
  haveI hloc : IsLocalization.AtPrime (A.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩

  letI algK : Algebra K Γ(A, V) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI hFT : Algebra.FiniteType K Γ(A, V) := by
    have h1 : RingHom.FiniteType (f.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
      ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv
    have h2 : ((f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).FiniteType :=
      h1.comp (RingHom.FiniteType.of_surjective _ hbij.surjective)
    exact h2
  letI : Module K H := Module.compHom H (algebraMap K Γ(A, V))
  haveI : IsScalarTower K Γ(A, V) H := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

  haveI : IsClosedImmersion κ := hκ
  haveI : IsFinite (κ ≫ f) := hfin
  have hKMfin : Set.Finite (Set.univ : Set KM) := by
    have := (κ ≫ f).finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun z _ => ?_
    show (κ ≫ f).base z ∈ ({IsLocalRing.closedPoint K} : Set _)
    exact Subsingleton.elim _ _
  haveI : Finite KM := Set.finite_univ_iff.mp hKMfin
  have hTfin : Set.Finite {𝔪 : MaximalSpectrum Γ(A, V) | hV.fromSpec.base 𝔪.toPrimeSpectrum ∈ Set.range κ.base} := by
    refine Set.Finite.preimage (f := fun 𝔪 : MaximalSpectrum Γ(A, V) => hV.fromSpec.base 𝔪.toPrimeSpectrum) ?_ (Set.finite_range κ.base)
    intro a _ b _ hab
    exact MaximalSpectrum.toPrimeSpectrum_injective (hV.fromSpec.isOpenEmbedding.injective hab)
  have hT : ∀ 𝔪 : MaximalSpectrum Γ(A, V), 𝔪 ∉ hTfin.toFinset → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
    intro 𝔪 h𝔪
    refine hH 𝔪 ?_
    simpa using h𝔪
  have hfl := (Module.finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton K Γ(A, V) H hTfin.toFinset hT).2.1
  exact Module.exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime Γ(A, V) H hfl
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal (A.presheaf.stalk y)

theorem partT
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) (V : A.Opens) (hV : IsAffineOpen V) (hyV : y ∈ V) :
    letI tV : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K) := hV.fromSpec ≫ f
    letI xV : SchemeHomOver tV f := ⟨hV.fromSpec, rfl⟩
    letI πV : pullback f tV ⟶ Spec (CommRingCat.of Γ(A, V)) := pullback.snd f tV
    letI MV : (pullback f tV).Modules :=
      (Scheme.Modules.pullback (sliceAt f xV)).obj (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tV) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰 : (pullback f tV).OrderedAffineCover := 𝒦.comap (pullback.fst f tV)
    letI GV := OModulePresheaf.ofModules πV MV
    letI algR : Algebra Γ(A, V) (A.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
    (∃ n : ℕ, IsLocalRing.maximalIdeal (A.presheaf.stalk y) ^ n •
      (⊤ : Submodule (A.presheaf.stalk y) (TensorProduct Γ(A, V) (A.presheaf.stalk y) (GV.H0 𝒰))) = ⊥) ∧
    ∀ i : ℕ, ∃ n : ℕ, IsLocalRing.maximalIdeal (A.presheaf.stalk y) ^ n •
      (⊤ : Submodule (A.presheaf.stalk y) (TensorProduct Γ(A, V) (A.presheaf.stalk y) (GV.HSucc 𝒰 i))) = ⊥ := by
  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : IsNoetherianRing Γ(A, V) := isNoetherianRing_sections_of_isAffineOpen K f V hV
  have hF : Scheme.Modules.IsInvertible (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) := by
    refine Scheme.Modules.IsInvertible.tensor_monoidalV2 ?_ (hN.pullback _)
    unfold mumfordBundle
    exact (hM.pullback _).tensor_monoidalV2 ((hM.dual_monoidalV2.1.pullback _).tensor_monoidalV2 (hM.dual_monoidalV2.1.pullback _))
  have htrivV := (hF.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)) f))).exists_trivialization
  haveI : IsAffineHom (pullback.fst f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))) := MorphismProperty.pullback_fst _ _ inferInstance
  have hCF := AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial (pullback.snd f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))) ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)) f))).obj (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)) htrivV (𝒦.comap (pullback.fst f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))))
  have hL2 := AlgebraicGeometry.Polarisation.subsingleton_localizedModule_cech_comap_of_not_mem_range_of_isAffineOpen
    K f L hc hA M hM κ hκ hfin hK N hN 𝒦 V hV
  have hCF0 := hCF.1
  have hCFS := hCF.2
  refine ⟨?_, fun i => ?_⟩
  · haveI := hCF0
    exact torsion_of_offKappa K f L hc hA g M hM κ hκ hfin hK N hN 𝒦 h𝒦 y V hV hyV _ (fun 𝔪 h𝔪 => (hL2 𝔪 h𝔪).1)
  · haveI := hCFS i
    exact torsion_of_offKappa K f L hc hA g M hM κ hκ hfin hK N hN 𝒦 h𝒦 y V hV hyV _ (fun 𝔪 h𝔪 => (hL2 𝔪 h𝔪).2 i)

theorem partA0
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) (V : A.Opens) (hV : IsAffineOpen V) (hyV : y ∈ V) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules (pullback.snd f tR) FR
    letI tV : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K) := hV.fromSpec ≫ f
    letI xV : SchemeHomOver tV f := ⟨hV.fromSpec, rfl⟩
    letI πV : pullback f tV ⟶ Spec (CommRingCat.of Γ(A, V)) := pullback.snd f tV
    letI MV : (pullback f tV).Modules :=
      (Scheme.Modules.pullback (sliceAt f xV)).obj (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tV) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰 : (pullback f tV).OrderedAffineCover := 𝒦.comap (pullback.fst f tV)
    letI GV := OModulePresheaf.ofModules πV MV
    letI algR : Algebra Γ(A, V) R := TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
    Nonempty (G.H0 𝒦R ≃ₗ[R] TensorProduct Γ(A, V) R (GV.H0 𝒰)) := by
  haveI : IsProper f := hA.proper
  letI algR : Algebra Γ(A, V) (A.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
  haveI hloc : IsLocalization.AtPrime (A.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  haveI hflat : Module.Flat Γ(A, V) (A.presheaf.stalk y) :=
    IsLocalization.flat (A.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
  have hx : A.fromSpecStalk y = (Scheme.TwoAffineOpenCover.specMap Γ(A, V) (A.presheaf.stalk y)) ≫ hV.fromSpec := by
    rw [← hV.fromSpecStalk_eq_fromSpecStalk hyV]
    rfl
  have hF : Scheme.Modules.IsInvertible (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) := by
    refine Scheme.Modules.IsInvertible.tensor_monoidalV2 ?_ (hN.pullback _)
    unfold mumfordBundle
    exact (hM.pullback _).tensor_monoidalV2 ((hM.dual_monoidalV2.1.pullback _).tensor_monoidalV2 (hM.dual_monoidalV2.1.pullback _))
  have htrivV := (hF.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)) f))).exists_trivialization
  haveI : IsAffineHom (pullback.fst f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))) := MorphismProperty.pullback_fst _ _ inferInstance
  have hL1 := @AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
    K _ A f inferInstance (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) hF 𝒦 V hV
    (A.presheaf.stalk y) _ algR (A.fromSpecStalk y ≫ f) ⟨A.fromSpecStalk y, rfl⟩ hx
  have hEE := (@AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
    Γ(A, V) _ _ (pullback.snd f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))) inferInstance (𝒦.comap (pullback.fst f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)))) ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)) f))).obj (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)) htrivV (A.presheaf.stalk y) _ algR).2 hflat
  have hL1a := hL1.1
  obtain ⟨e0⟩ := hL1a
  have hEEa := hEE.1
  obtain ⟨b0⟩ := hEEa
  exact ⟨e0.trans b0⟩

theorem partAS
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) (V : A.Opens) (hV : IsAffineOpen V) (hyV : y ∈ V) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules (pullback.snd f tR) FR
    letI tV : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K) := hV.fromSpec ≫ f
    letI xV : SchemeHomOver tV f := ⟨hV.fromSpec, rfl⟩
    letI πV : pullback f tV ⟶ Spec (CommRingCat.of Γ(A, V)) := pullback.snd f tV
    letI MV : (pullback f tV).Modules :=
      (Scheme.Modules.pullback (sliceAt f xV)).obj (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tV) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰 : (pullback f tV).OrderedAffineCover := 𝒦.comap (pullback.fst f tV)
    letI GV := OModulePresheaf.ofModules πV MV
    letI algR : Algebra Γ(A, V) R := TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
    ∀ i : ℕ, Nonempty (G.HSucc 𝒦R i ≃ₗ[R] TensorProduct Γ(A, V) R (GV.HSucc 𝒰 i)) := by
  haveI : IsProper f := hA.proper
  letI algR : Algebra Γ(A, V) (A.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
  haveI hloc : IsLocalization.AtPrime (A.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  haveI hflat : Module.Flat Γ(A, V) (A.presheaf.stalk y) :=
    IsLocalization.flat (A.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
  have hx : A.fromSpecStalk y = (Scheme.TwoAffineOpenCover.specMap Γ(A, V) (A.presheaf.stalk y)) ≫ hV.fromSpec := by
    rw [← hV.fromSpecStalk_eq_fromSpecStalk hyV]
    rfl
  have hF : Scheme.Modules.IsInvertible (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) := by
    refine Scheme.Modules.IsInvertible.tensor_monoidalV2 ?_ (hN.pullback _)
    unfold mumfordBundle
    exact (hM.pullback _).tensor_monoidalV2 ((hM.dual_monoidalV2.1.pullback _).tensor_monoidalV2 (hM.dual_monoidalV2.1.pullback _))
  have htrivV := (hF.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)) f))).exists_trivialization
  haveI : IsAffineHom (pullback.fst f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))) := MorphismProperty.pullback_fst _ _ inferInstance
  have hL1 := @AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
    K _ A f inferInstance (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) hF 𝒦 V hV
    (A.presheaf.stalk y) _ algR (A.fromSpecStalk y ≫ f) ⟨A.fromSpecStalk y, rfl⟩ hx
  have hEE := (@AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
    Γ(A, V) _ _ (pullback.snd f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K))) inferInstance (𝒦.comap (pullback.fst f (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)))) ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K)) f))).obj (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)) htrivV (A.presheaf.stalk y) _ algR).2 hflat
  intro i
  have hL1b := hL1.2
  have hL1c := hL1b i
  obtain ⟨ei⟩ := hL1c
  have hEEb := hEE.2
  have hbi := hEEb i
  obtain ⟨bi⟩ := hbi
  exact ⟨ei.trans bi⟩

open StalkTorsionAux in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules (pullback.snd f tR) FR
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R (G.H0 𝒦R)) = ⊥ ∧
      ∀ i : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R (G.HSucc 𝒦R i)) = ⊥ := by
  classical
  have hV0 := exists_isAffineOpen_mem_and_subset (X := A) (x := y) (U := ⊤) trivial
  rcases hV0 with ⟨V, hV, hyV, hsub⟩
  letI algR : Algebra Γ(A, V) (A.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk A.presheaf (⟨y, hyV⟩ : (V : A.Opens))
  have hT := partT K f L hc hA g M hM κ hκ hfin hK N hN 𝒦 h𝒦 y V hV hyV
  have hT0 := hT.1
  have hTS := hT.2
  have hA0 := partA0 K f L hc hA g M hM κ hκ hfin hK N hN 𝒦 h𝒦 y V hV hyV
  have hAS := partAS K f L hc hA g M hM κ hκ hfin hK N hN 𝒦 h𝒦 y V hV hyV
  obtain ⟨e0⟩ := hA0
  obtain ⟨n0, hn0⟩ := hT0
  have key0 := smul_top_eq_bot_of_linearEquiv _ e0 hn0
  choose nS hnS using hTS
  refine ⟨n0 + ∑ i ∈ Finset.range (Fintype.card 𝒦.ι), nS i, ?_, fun i => ?_⟩
  · exact pow_smul_top_eq_bot_mono _ (Nat.le_add_right _ _) key0
  · by_cases hi : i < Fintype.card 𝒦.ι
    · have hle : nS i ≤ n0 + ∑ j ∈ Finset.range (Fintype.card 𝒦.ι), nS j :=
        le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (nS j)) (Finset.mem_range.mpr hi))
      have hASi := hAS i
      obtain ⟨ei⟩ := hASi
      exact pow_smul_top_eq_bot_mono _ hle (smul_top_eq_bot_of_linearEquiv _ ei (hnS i))
    · exact @smul_top_eq_bot_of_subsingleton _ _ _ _ _
        (subsingleton_HSucc_of_card_lt _ _ i (by show Fintype.card 𝒦.ι < i + 2; omega)) _

end S_AlgebraicGeometry_Polarisation_exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot (solution)
