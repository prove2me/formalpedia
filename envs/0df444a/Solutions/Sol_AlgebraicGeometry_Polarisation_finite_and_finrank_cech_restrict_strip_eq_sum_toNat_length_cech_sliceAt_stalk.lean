-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4eb8d7ef-5e9a-538c-a4df-067f84933369

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
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec
import Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_localizedModule_cech_comap_of_not_mem_range_of_isAffineOpen
import Theorems.Thm_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation TensorProduct"

universe u v w

namespace LocLength

theorem length_eq_of_bijective {R : Type u} {R' : Type v} [Ring R] [Ring R'] (σ : R →+* R') [RingHomSurjective σ]
    {M : Type w} {M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[σ] M') (hf : Function.Bijective f) : Module.length R M = Module.length R' M' := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

end LocLength

namespace StripReduce

theorem locLength
    {S : Type} [CommRing S] (𝔭 : Ideal S) [𝔭.IsPrime]
    (B : Type) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B 𝔭]
    (H : Type) [AddCommGroup H] [Module S H] :
    Module.length (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl H) = Module.length B (B ⊗[S] H) := by
  classical
  let σ : Localization.AtPrime 𝔭 ≃ₐ[S] B := Localization.algEquiv 𝔭.primeCompl B
  haveI : RingHomSurjective (σ : Localization.AtPrime 𝔭 →+* B) := ⟨σ.surjective⟩

  let τ : Localization.AtPrime 𝔭 ⊗[S] H ≃ₗ[S] B ⊗[S] H := TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl S H)
  have hτ : ∀ (l : Localization.AtPrime 𝔭) (x : Localization.AtPrime 𝔭 ⊗[S] H), τ (l • x) = σ l • τ x := by
    intro l x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a h =>
      simp only [τ, TensorProduct.smul_tmul', TensorProduct.congr_tmul, LinearEquiv.refl_apply, smul_eq_mul]
      rw [show σ.toLinearEquiv (l * a) = σ l * σ a from map_mul σ l a]
      rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

  let e₁ := LocalizedModule.equivTensorProduct 𝔭.primeCompl H
  let f : LocalizedModule 𝔭.primeCompl H →ₛₗ[(σ : Localization.AtPrime 𝔭 →+* B)] B ⊗[S] H :=
    { toFun := fun m => τ (e₁ m)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun l m => by
        simp only [LinearEquiv.map_smul, RingHom.coe_coe]
        exact hτ l (e₁ m) }
  have hf : Function.Bijective f := (τ.bijective).comp e₁.bijective
  exact LocLength.length_eq_of_bijective (σ : Localization.AtPrime 𝔭 →+* B) f hf

theorem isClosed_singleton_base
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f)) (y' : KM) :
    IsClosed ({κ.base y'} : Set A) := by
  haveI := hκ
  haveI := hfin

  obtain ⟨hAff, hmod⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).1 (inferInstance : IsFinite (κ ≫ f))
  letI : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(KM, ⊤) := (κ ≫ f).appTop.hom.toAlgebra
  haveI : Module.Finite Γ(Spec (CommRingCat.of K), ⊤) Γ(KM, ⊤) := hmod
  have hF : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  letI : Field Γ(Spec (CommRingCat.of K), ⊤) := hF.toField
  haveI : IsArtinianRing Γ(KM, ⊤) := IsArtinianRing.of_finite Γ(Spec (CommRingCat.of K), ⊤) _
  haveI : IsAffine KM := hAff

  have hy' : IsClosed ({y'} : Set KM) := by
    let h := Scheme.homeoOfIso KM.isoSpec
    have : ({y'} : Set KM) = h ⁻¹' {h y'} := by
      ext z; simp [h.injective.eq_iff]
    rw [this]
    exact (isClosed_singleton (x := h y')).preimage h.continuous
  have := (Scheme.Hom.isClosedEmbedding κ).isClosedMap _ hy'
  rwa [Set.image_singleton] at this

theorem isMaximal_primeIdealOf_base
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (V : A.Opens) (hV : IsAffineOpen V) (y' : KM) (hy : κ.base y' ∈ V) :
    ((hV.primeIdealOf ⟨κ.base y', hy⟩).asIdeal).IsMaximal :=
  hV.primeIdealOf_isMaximal_of_isClosed ⟨κ.base y', hy⟩ (isClosed_singleton_base K f κ hκ hfin y')

theorem primeIdealOf_base_injective
    {A : Scheme.{0}} {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ)
    (V : A.Opens) (hV : IsAffineOpen V) (y₁ y₂ : KM) (h₁ : κ.base y₁ ∈ V) (h₂ : κ.base y₂ ∈ V)
    (h : hV.primeIdealOf ⟨κ.base y₁, h₁⟩ = hV.primeIdealOf ⟨κ.base y₂, h₂⟩) : y₁ = y₂ := by
  haveI := hκ
  apply (Scheme.Hom.isClosedEmbedding κ).injective
  have e₁ := hV.fromSpec_primeIdealOf ⟨κ.base y₁, h₁⟩
  have e₂ := hV.fromSpec_primeIdealOf ⟨κ.base y₂, h₂⟩
  rw [h] at e₁
  exact e₁.symm.trans e₂

theorem exists_eq_primeIdealOf_base
    {A : Scheme.{0}} {KM : Scheme.{0}} (κ : KM ⟶ A)
    (V : A.Opens) (hV : IsAffineOpen V) (𝔪 : MaximalSpectrum ↥Γ(A, V))
    (h𝔪 : hV.fromSpec.base 𝔪.toPrimeSpectrum ∈ Set.range κ.base) :
    ∃ (y' : KM) (hy : κ.base y' ∈ V), 𝔪.toPrimeSpectrum = hV.primeIdealOf ⟨κ.base y', hy⟩ := by
  obtain ⟨y', hy'⟩ := h𝔪
  have hV' : hV.fromSpec.base 𝔪.toPrimeSpectrum ∈ (V : Set A) := by
    rw [← hV.range_fromSpec]; exact ⟨_, rfl⟩
  refine ⟨y', hy' ▸ hV', ?_⟩
  apply (Scheme.Hom.isOpenEmbedding hV.fromSpec).injective
  rw [hV.fromSpec_primeIdealOf]
  exact hy'.symm

theorem finiteType_sections
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (V : A.Opens) (hV : IsAffineOpen V) :
    letI : Algebra K ↥Γ(A, V) := Scheme.TwoAffineOpenCover.algebraOfHom f V
    Algebra.FiniteType K ↥Γ(A, V) := by
  have h1 : (f.appLE ⊤ V le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of K))) hV le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective
  exact h1.comp h2

theorem finite_cech_slice_chart
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsProper f] [LocallyOfFiniteType f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒦 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V) :
    letI S : Type := ↥Γ(A, V)
    letI σ : Spec (CommRingCat.of S) ⟶ A := hV.fromSpec
    letI tS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K) := σ ≫ f
    letI xS : SchemeHomOver tS f := ⟨σ, rfl⟩
    letI FS : (pullback f tS).Modules := (Scheme.Modules.pullback (sliceAt f xS)).obj F
    letI _ : IsAffineHom (pullback.fst f tS) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰S : (pullback f tS).OrderedAffineCover := 𝒦.comap (pullback.fst f tS)
    letI GS := OModulePresheaf.ofModules (pullback.snd f tS) FS
    Module.Finite S ↥(GS.H0 𝒰S) ∧ ∀ i : ℕ, Module.Finite S (GS.HSucc 𝒰S i) := by
  letI : Algebra K ↥Γ(A, V) := Scheme.TwoAffineOpenCover.algebraOfHom f V
  haveI : Algebra.FiniteType K ↥Γ(A, V) := finiteType_sections K f V hV
  haveI : IsNoetherianRing ↥Γ(A, V) := Algebra.FiniteType.isNoetherianRing K _
  exact (OModulePresheaf.cechFinite_iff _ _).1
    (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial (pullback.snd f (hV.fromSpec ≫ f)) _
      (hF.pullback _).exists_trivialization _)

theorem perPoint
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsSeparated f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒦 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V) (y : A) (hy : y ∈ V) :

    letI S : Type := ↥Γ(A, V)
    letI σ : Spec (CommRingCat.of S) ⟶ A := hV.fromSpec
    letI tS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K) := σ ≫ f
    letI xS : SchemeHomOver tS f := ⟨σ, rfl⟩
    letI FS : (pullback f tS).Modules := (Scheme.Modules.pullback (sliceAt f xS)).obj F
    letI _ : IsAffineHom (pullback.fst f tS) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰S : (pullback f tS).OrderedAffineCover := 𝒦.comap (pullback.fst f tS)
    letI GS := OModulePresheaf.ofModules (pullback.snd f tS) FS
    letI 𝔪 : Ideal S := (hV.primeIdealOf ⟨y, hy⟩).asIdeal

    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI FR : (pullback f tR).Modules := (Scheme.Modules.pullback (sliceAt f xR)).obj F
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI Gy := OModulePresheaf.ofModules (pullback.snd f tR) FR
    Module.length (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl ↥(GS.H0 𝒰S)) = Module.length R ↥(Gy.H0 𝒦R) ∧
      ∀ q : ℕ, Module.length (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl (GS.HSucc 𝒰S q)) =
        Module.length R (Gy.HSucc 𝒦R q) := by
  classical

  letI alg : Algebra ↥Γ(A, V) ↥(A.presheaf.stalk y) := A.presheaf.algebra_section_stalk ⟨y, hy⟩
  haveI hloc : IsLocalization.AtPrime (↥(A.presheaf.stalk y)) (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hy⟩
  have hflat : Module.Flat ↥Γ(A, V) ↥(A.presheaf.stalk y) :=
    IsLocalization.flat _ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl

  have hx : A.fromSpecStalk y =
      Scheme.TwoAffineOpenCover.specMap ↥Γ(A, V) ↥(A.presheaf.stalk y) ≫ hV.fromSpec := by
    rw [← hV.fromSpecStalk_eq_fromSpecStalk hy, IsAffineOpen.fromSpecStalk]
    change Spec.map (A.presheaf.germ V y hy) ≫ hV.fromSpec =
      Spec.map (CommRingCat.ofHom (A.presheaf.germ V y hy).hom) ≫ hV.fromSpec
    rw [CommRingCat.ofHom_hom]

  have hS := @AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
    K _ A f _ F hF 𝒦 V hV ↥(A.presheaf.stalk y) _ alg (A.fromSpecStalk y ≫ f) ⟨A.fromSpecStalk y, rfl⟩ hx

  haveI : IsSeparated (pullback.snd f (hV.fromSpec ≫ f)) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsAffineHom (pullback.fst f (hV.fromSpec ≫ f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have htriv := (hF.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).exists_trivialization
  have hB := (AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
    (pullback.snd f (hV.fromSpec ≫ f)) (𝒦.comap (pullback.fst f (hV.fromSpec ≫ f)))
    ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj F)
    htriv ↥(A.presheaf.stalk y)).2 hflat
  refine ⟨?_, fun q => ?_⟩
  · exact (locLength (hV.primeIdealOf ⟨y, hy⟩).asIdeal ↥(A.presheaf.stalk y) _).trans
      ((hS.1.some.trans hB.1.some).length_eq).symm
  · exact (locLength (hV.primeIdealOf ⟨y, hy⟩).asIdeal ↥(A.presheaf.stalk y) _).trans
      (((hS.2 q).some.trans (hB.2 q).some).length_eq).symm

theorem isInvertible_F
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (N : A.Modules) (hN : Scheme.Modules.IsInvertible N) :
    Scheme.Modules.IsInvertible (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) := by
  have hd : Scheme.Modules.IsInvertible (Scheme.Modules.dual M) := (Scheme.Modules.IsInvertible.dual_monoidalV2 hM).1
  refine Scheme.Modules.IsInvertible.tensor_monoidalV2 ?_ (Scheme.Modules.IsInvertible.pullback _ hN)
  unfold mumfordBundle
  exact Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ hM)
    (Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ hd)
      (Scheme.Modules.IsInvertible.pullback _ hd))

theorem chartCount
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (V : A.Opens) (hV : IsAffineOpen V) (TV : Finset KM) (hTV : ∀ y' : KM, y' ∈ TV ↔ κ.base y' ∈ V)
    (H : Type) [AddCommGroup H] [Module ↥Γ(A, V) H] [Module.Finite ↥Γ(A, V) H]
    (off : ∀ 𝔪 : MaximalSpectrum ↥Γ(A, V), hV.fromSpec.base 𝔪.toPrimeSpectrum ∉ Set.range κ.base →
      Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H))
    (ℓ : KM → ℕ∞)
    (per : ∀ (y' : KM) (hy : κ.base y' ∈ V),
      Module.length (Localization.AtPrime (hV.primeIdealOf ⟨κ.base y', hy⟩).asIdeal)
        (LocalizedModule (hV.primeIdealOf ⟨κ.base y', hy⟩).asIdeal.primeCompl H) = ℓ y') :
    letI : Algebra K ↥Γ(A, V) := Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI : Module K H := Module.compHom H (algebraMap K ↥Γ(A, V))
    Module.Finite K H ∧ Module.finrank K H = ∑ y' ∈ TV, (ℓ y').toNat := by
  classical
  letI alg : Algebra K ↥Γ(A, V) := Scheme.TwoAffineOpenCover.algebraOfHom f V
  letI modK : Module K H := Module.compHom H (algebraMap K ↥Γ(A, V))
  haveI : IsScalarTower K ↥Γ(A, V) H :=
    ⟨fun k s h => by
      change (algebraMap K ↥Γ(A, V) k * s) • h = algebraMap K ↥Γ(A, V) k • (s • h)
      rw [mul_smul]⟩
  haveI : Algebra.FiniteType K ↥Γ(A, V) := finiteType_sections K f V hV

  let mx : ↥TV → MaximalSpectrum ↥Γ(A, V) := fun y' =>
    ⟨(hV.primeIdealOf ⟨κ.base y'.1, (hTV y'.1).mp y'.2⟩).asIdeal,
      isMaximal_primeIdealOf_base K f κ hκ hfin V hV y'.1 ((hTV y'.1).mp y'.2)⟩
  have hmx_inj : Function.Injective mx := by
    intro a b hab
    apply Subtype.ext
    apply primeIdealOf_base_injective κ hκ V hV a.1 b.1 ((hTV a.1).mp a.2) ((hTV b.1).mp b.2)
    apply PrimeSpectrum.ext
    exact congrArg MaximalSpectrum.asIdeal hab
  let T' : Finset (MaximalSpectrum ↥Γ(A, V)) := TV.attach.image mx
  have hT' : ∀ 𝔪 : MaximalSpectrum ↥Γ(A, V), 𝔪 ∉ T' → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
    intro 𝔪 h𝔪
    apply off 𝔪
    intro hmem
    apply h𝔪
    obtain ⟨y', hy, heq⟩ := exists_eq_primeIdealOf_base κ V hV 𝔪 hmem
    refine Finset.mem_image.mpr ⟨⟨y', (hTV y').mpr hy⟩, Finset.mem_attach _ _, ?_⟩
    apply MaximalSpectrum.ext
    change (hV.primeIdealOf ⟨κ.base y', hy⟩).asIdeal = 𝔪.asIdeal
    rw [← heq]
    rfl
  have hFS := Module.finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton K ↥Γ(A, V) H T' hT'
  refine ⟨hFS.1, ?_⟩
  have hsum := hFS.2.2
  rw [Finset.sum_image (fun a _ b _ h => hmx_inj h)] at hsum
  have hsum' : (Module.finrank K H : ℕ∞) = ∑ y' ∈ TV, ℓ y' := by
    rw [hsum, ← Finset.sum_attach TV (fun y' => ℓ y')]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact per x.1 ((hTV x.1).mp x.2)

  have hne : ∀ y' ∈ TV, ℓ y' ≠ ⊤ := by
    intro y' hy'
    refine ne_top_of_le_ne_top ?_ (Finset.single_le_sum (f := fun y' => ℓ y') (fun i _ => zero_le) hy')
    rw [← hsum']
    exact ENat.coe_ne_top _
  have : (∑ y' ∈ TV, ℓ y') = ((∑ y' ∈ TV, (ℓ y').toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun y' hy' => (ENat.coe_toNat (hne y' hy')).symm)
  rw [this] at hsum'
  exact_mod_cast hsum'

end StripReduce

open StripReduce in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover)
    (V : A.Opens) (hV : IsAffineOpen V)
    (W : (pullback f f).Opens) (hW : W = (pullback.snd f f) ⁻¹ᵁ V)
    (𝔚 : (W : Scheme.{0}).OrderedAffineCover)
    (TV : Finset KM) (hTV : ∀ y' : KM, y' ∈ TV ↔ κ.base y' ∈ V) :
    letI F : (pullback f f).Modules := mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N
    letI GW := OModulePresheaf.ofModules (W.ι ≫ pullback.fst f f ≫ f) (F.restrict W.ι)
    (Module.Finite K (GW.H0 𝔚) ∧
      Module.finrank K (GW.H0 𝔚) =
        ∑ y' ∈ TV,
          letI y : A := κ.base y'
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
          (Module.length R (G.H0 𝒦R)).toNat) ∧
    ∀ i : ℕ, Module.Finite K (GW.HSucc 𝔚 i) ∧
      Module.finrank K (GW.HSucc 𝔚 i) =
        ∑ y' ∈ TV,
          letI y : A := κ.base y'
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
          (Module.length R (G.HSucc 𝒦R i)).toNat := by
  classical
  haveI : IsProper f := hA.proper
  have hF := isInvertible_F K f L M hM N hN

  have hD := @AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec K _ A f _
    (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) hF 𝒦 V hV W hW 𝔚
  have hOff := AlgebraicGeometry.Polarisation.subsingleton_localizedModule_cech_comap_of_not_mem_range_of_isAffineOpen
    K f L hc hA M hM κ hκ hfin hK N hN 𝒦 V hV
  have hFinS := finite_cech_slice_chart K f (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) hF 𝒦 V hV
  have hPP := fun (y' : KM) (hy : κ.base y' ∈ V) =>
    perPoint K f (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N) hF 𝒦 V hV (κ.base y') hy
  letI algKS : Algebra K ↥Γ(A, V) := Scheme.TwoAffineOpenCover.algebraOfHom f V
  haveI hAffV : IsAffineHom (pullback.fst f (hV.fromSpec ≫ f)) := MorphismProperty.pullback_fst _ _ inferInstance

  haveI := hFinS.1
  have c0 := chartCount K f κ hκ hfin V hV TV hTV _ (fun 𝔪 h => (hOff 𝔪 h).1)
    (fun y' : KM =>
      letI y : A := κ.base y'
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
      Module.length R ↥(G.H0 𝒦R)) (fun y' hy => (hPP y' hy).1)
  refine ⟨?_, fun i => ?_⟩
  · have e0 := hD.1.some
    letI : Module K ↥((OModulePresheaf.ofModules (pullback.snd f (hV.fromSpec ≫ f))
        ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj
          (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N))).H0
        (𝒦.comap (pullback.fst f (hV.fromSpec ≫ f)))) := Module.compHom _ (algebraMap K ↥Γ(A, V))
    haveI := c0.1
    exact ⟨Module.Finite.equiv e0.symm, e0.finrank_eq.trans c0.2⟩
  · haveI := hFinS.2 i
    have ci := chartCount K f κ hκ hfin V hV TV hTV _ (fun 𝔪 h => (hOff 𝔪 h).2 i)
      (fun y' : KM =>
      letI y : A := κ.base y'
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
      Module.length R (G.HSucc 𝒦R i)) (fun y' hy => (hPP y' hy).2 i)
    have ei := (hD.2 i).some
    letI : Module K ((OModulePresheaf.ofModules (pullback.snd f (hV.fromSpec ≫ f))
        ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj
          (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N))).HSucc
        (𝒦.comap (pullback.fst f (hV.fromSpec ≫ f))) i) := Module.compHom _ (algebraMap K ↥Γ(A, V))
    haveI := ci.1
    exact ⟨Module.Finite.equiv ei.symm, ei.finrank_eq.trans ci.2⟩

end S_AlgebraicGeometry_Polarisation_finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk (solution)
