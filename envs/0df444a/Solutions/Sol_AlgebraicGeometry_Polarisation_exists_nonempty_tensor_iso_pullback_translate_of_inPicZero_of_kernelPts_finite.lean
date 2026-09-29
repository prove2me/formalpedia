-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f7ea2fdb-c049-5b64-8d91-1071d5d3e122

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Polarisation_H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_pullback_translate_tensor_dual
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fst_translate_tensor_dual
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_leftSlice_mumfordBundle_iso_pullback_translate_tensor_dual
import Theorems.Thm_AlgebraicGeometry_Polarisation_InPicZero_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_InPicZero_dual
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_subsingleton_HSucc_restrict_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_comp_point_iso_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules
import Theorems.Thm_IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_tensorUnit_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.injEq CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"
p2m_attr_erase "simp" "PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation TensorProduct"

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u

namespace L4Asm

p2m_open "AlgebraicGeometry.OModulePresheaf~tensor~ker AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem submodule_eq_bot_of_equiv {R : Type u} [CommRing R] {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {p : Submodule R M₁} {q : Submodule R M₂} (e : p ≃ₗ[R] q) (h : p = ⊥) :
    q = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h1 : e.symm ⟨x, hx⟩ = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff p).mp h _ (e.symm ⟨x, hx⟩).2)
  have h2 : (⟨x, hx⟩ : q) = 0 := by
    rw [← e.apply_symm_apply ⟨x, hx⟩, h1, map_zero]
  exact congrArg Subtype.val h2

theorem van_iff_of_iso {R : Type u} [CommRing R] {P : Scheme.{u}} (π : P ⟶ Spec (.of R)) {N N' : P.Modules}
    (e : N ≅ N') (𝔚 : P.OrderedAffineCover) :
    ((ofModules π N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules π N).HSucc 𝔚 j)) ↔
      ((ofModules π N').H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules π N').HSucc 𝔚 j)) := by
  obtain ⟨⟨q0⟩, qS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e 𝔚
  constructor
  · rintro ⟨h0, hS⟩
    exact ⟨submodule_eq_bot_of_equiv q0 h0, fun j => by obtain ⟨q⟩ := qS j; exact q.symm.toEquiv.subsingleton⟩
  · rintro ⟨h0, hS⟩
    exact ⟨submodule_eq_bot_of_equiv q0.symm h0, fun j => by obtain ⟨q⟩ := qS j; exact q.toEquiv.subsingleton⟩

theorem isInvertible_of_iso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M') (h : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.IsInvertible M' := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨eU⟩⟩ := h.exists_trivialization x
  exact ⟨U, hx, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

theorem isInvertible_tensorUnit (X : Scheme.{u}) : Scheme.Modules.IsInvertible (𝟙_ X.Modules) :=
  Scheme.Modules.isInvertible_unit X

noncomputable def isoPullbackInv {P P' : Scheme.{u}} (Φ : P ⟶ P') [IsIso Φ] (N' : P'.Modules) (X : P.Modules)
    (e : (Scheme.Modules.pullback Φ).obj N' ≅ X) : N' ≅ (Scheme.Modules.pullback (inv Φ)).obj X :=
  ((Scheme.Modules.pullbackId P').app N').symm ≪≫ (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id Φ).symm).app N' ≪≫
    ((Scheme.Modules.pullbackComp (inv Φ) Φ).app N').symm ≪≫ (Scheme.Modules.pullback (inv Φ)).mapIso e

noncomputable def pullbackCompIso' {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c)
    (N : Z.Modules) :
    (Scheme.Modules.pullback c).obj N ≅ (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj N) :=
  (Scheme.Modules.pullbackCongr h.symm).app N ≪≫ ((Scheme.Modules.pullbackComp a b).app N).symm

noncomputable def restrictIsoPullback {X Y : Scheme.{u}} (N : Y.Modules) (ι : X ⟶ Y) [IsOpenImmersion ι] :
    N.restrict ι ≅ (Scheme.Modules.pullback ι).obj N :=
  (Scheme.Modules.restrictFunctorIsoPullback ι).app N

noncomputable def coverComap {P P' : Scheme.{u}} (Φ : P ⟶ P') [IsIso Φ] (𝔚 : P'.OrderedAffineCover) :
    P.OrderedAffineCover :=
  𝔚.comap Φ

theorem van_transfer {R R' : Type u} [CommRing R] [CommRing R'] {P P' : Scheme.{u}}
    (π : P ⟶ Spec (.of R)) (π' : P' ⟶ Spec (.of R')) [IsSeparated π'] (Φ : P ⟶ P') [IsIso Φ]
    (N' : P'.Modules) (hN' : Scheme.Modules.IsInvertible N') (N : P.Modules)
    (e : N ≅ (Scheme.Modules.pullback Φ).obj N') (𝔚' : P'.OrderedAffineCover)
    (h : (ofModules π' N').H0 𝔚' = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules π' N').HSucc 𝔚' j))
    (𝔚 : P.OrderedAffineCover) :
    (ofModules π N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules π N).HSucc 𝔚 j) := by
  have h1 := OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso π' Φ N' hN' N e 𝔚' h 𝔚
  exact (OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules (Φ ≫ π') π N 𝔚).mp h1

theorem van_any_cover {R : Type u} [CommRing R] {P : Scheme.{u}} (π : P ⟶ Spec (.of R)) [IsSeparated π]
    (N : P.Modules) (hN : Scheme.Modules.IsInvertible N) (𝔚' : P.OrderedAffineCover)
    (h : (ofModules π N).H0 𝔚' = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules π N).HSucc 𝔚' j))
    (𝔚 : P.OrderedAffineCover) :
    (ofModules π N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules π N).HSucc 𝔚 j) :=
  van_transfer π π (𝟙 P) N hN N ((Scheme.Modules.pullbackId P).app N).symm 𝔚' h 𝔚

theorem flat_baseChange_inter {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (B : Type u) [CommRing B] [Algebra k B] (i : ℕ) (s : (𝒰.baseChange π B).Idx i) :
    letI := algebraOfHom (pullback.snd π (specMap k B)) ((𝒰.baseChange π B).inter s)
    Module.Flat B Γ(pullback π (specMap k B), (𝒰.baseChange π B).inter s) := by
  letI i1 := algebraOfHom π (𝒰.inter s)
  letI i2 := algebraOfHom (pullback.snd π (specMap k B)) ((𝒰.baseChange π B).inter s)
  obtain ⟨σ, -, hσ⟩ := Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter π 𝒰 B s
  have hlin : ∀ (b : B) (x : B ⊗[k] Γ(X, 𝒰.inter s)), σ (b • x) = b • σ x := by
    intro b x
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      map_mul, hσ, ← Algebra.smul_def]
  let e : (B ⊗[k] Γ(X, 𝒰.inter s)) ≃ₗ[B] Γ(pullback π (specMap k B), (𝒰.baseChange π B).inter s) :=
    { toFun := σ, map_add' := fun x y => map_add σ x y, map_smul' := hlin, invFun := σ.symm,
      left_inv := σ.left_inv, right_inv := σ.right_inv }
  haveI : Module.Flat k Γ(X, 𝒰.inter s) := inferInstance
  exact Module.Flat.of_linearEquiv e.symm

theorem fromSpec_comp_eq_specMap {k : Type u} [CommRing k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI := algebraOfHom π V
    hV.fromSpec ≫ π = specMap k Γ(X, V) := by
  letI := algebraOfHom π V
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec π (isAffineOpen_top _) hV (le_top : V ≤ π ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h1
  rw [← h1]
  rfl

theorem P6w {k : Type u} [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (B : Type u) [CommRing B] [Algebra k B] (i : Spec (CommRingCat.of B) ⟶ A)
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)) (hg : i ≫ f = g)
    (hi : g = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (𝔪 : Ideal B) [𝔪.IsMaximal] (χ : B →ₐ[k] k) (hχ : ∀ b : B, b ∈ 𝔪 ↔ χ b = 0) :
    ∃ (Φ : A ⟶ pullback (pullback.snd f g) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪))),
      IsIso Φ ∧
      Φ ≫ pullback.fst (pullback.snd f g) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) ≫ pullback.fst f g = 𝟙 A ∧
      Φ ≫ pullback.fst (pullback.snd f g) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) ≫ pullback.snd f g =
        f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ∧
      Φ ≫ pullback.snd (pullback.snd f g) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) =
        f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift 𝔪 χ.toRingHom (fun b hb => (hχ b).mp hb))) ∧
      ∀ N : (pullback f f).Modules,
        Nonempty ((Scheme.Modules.pullback Φ).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f g) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj
            ((Scheme.Modules.pullback
              (pullback.lift (pullback.fst f g) (pullback.snd f g ≫ i)
                (by rw [Category.assoc, hg]; exact pullback.condition))).obj N)) ≅
          (Scheme.Modules.pullback
            (pullback.lift (𝟙 A) (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ i)
              (by rw [Category.id_comp, Category.assoc, Category.assoc, hg, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    show χ.toRingHom.comp (algebraMap k B) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
                    CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]))).obj N) := by
  subst hg
  exact Scheme.exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id f B i hi 𝔪 χ hχ

theorem nonempty_orderedAffineCover (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  let 𝒱 := X.affineCover.finiteSubcover
  letI : LinearOrder 𝒱.I₀ := LinearOrder.lift' (Fintype.equivFin 𝒱.I₀) (Fintype.equivFin 𝒱.I₀).injective
  exact ⟨Scheme.OrderedAffineCover.mk (ι := 𝒱.I₀) (U := fun j => (𝒱.f j).opensRange)
    (isAffineOpen := fun j => isAffineOpen_opensRange (𝒱.f j)) (iSup_eq_top := 𝒱.iSup_opensRange)⟩

noncomputable def dualTensorIso {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.dual L ⊗ L ≅ 𝟙_ X.Modules :=
  β_ _ _ ≪≫ (hL.dual_monoidalV2).2.some

noncomputable def isoOfTensorDualIsoUnit {X : Scheme.{u}} (T L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (e : T ⊗ Scheme.Modules.dual L ≅ 𝟙_ X.Modules) : T ≅ L :=
  (ρ_ T).symm ≪≫ whiskerLeftIso T (dualTensorIso hL).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e L ≪≫ λ_ L

noncomputable def isoOfTensorDualTensorDualIsoUnit {X : Scheme.{u}} (T L M : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (e : (T ⊗ Scheme.Modules.dual L) ⊗ Scheme.Modules.dual M ≅ 𝟙_ X.Modules) : M ⊗ L ≅ T :=
  whiskerRightIso (isoOfTensorDualIsoUnit _ M hM e).symm L ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso T (dualTensorIso hL) ≪≫ ρ_ T

section Slices

variable {k : Type} [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

noncomputable def rslice (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : A ⟶ pullback f f :=
  pullback.lift (𝟙 A) (f ≫ y.1) (by rw [Category.id_comp, Category.assoc, y.2, Category.comp_id])

noncomputable def lslice (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : A ⟶ pullback f f :=
  pullback.lift (f ≫ y.1) (𝟙 A) (by rw [Category.assoc, y.2, Category.comp_id, Category.id_comp])

omit [IsAlgClosed k] in
theorem rslice_fst (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : rslice f y ≫ pullback.fst f f = 𝟙 A :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
theorem rslice_snd (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : rslice f y ≫ pullback.snd f f = f ≫ y.1 :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
theorem lslice_fst (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : lslice f y ≫ pullback.fst f f = f ≫ y.1 :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
theorem lslice_snd (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : lslice f y ≫ pullback.snd f f = 𝟙 A :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
theorem rslice_symmetry (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    rslice f y ≫ (pullbackSymmetry f f).hom = lslice f y := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, rslice_snd, lslice_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, rslice_fst, lslice_snd]

theorem nonempty_rslice_mumfordBundle_iso (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty ((Scheme.Modules.pullback (rslice f y)).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by
  obtain ⟨e1⟩ := nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fst_translate_tensor_dual k f L 𝓛 h𝓛 y
  let τ : A ⟶ pullback f (𝟙 (Spec (CommRingCat.of k))) := pullback.lift (𝟙 A) f (by simp)
  have hτ : τ ≫ sliceAt f y = rslice f y := by
    apply pullback.hom_ext
    · rw [Category.assoc, sliceAt, pullback.lift_fst, pullback.lift_fst, rslice_fst]
    · rw [Category.assoc, sliceAt, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, rslice_snd]
  have hτ1 : τ ≫ pullback.fst f (𝟙 _) = 𝟙 A := pullback.lift_fst _ _ _
  exact ⟨pullbackCompIso' τ (sliceAt f y) (rslice f y) hτ _ ≪≫ (Scheme.Modules.pullback τ).mapIso e1 ≪≫
    (pullbackCompIso' τ (pullback.fst f (𝟙 _)) (𝟙 A) hτ1 _).symm ≪≫ (Scheme.Modules.pullbackId A).app _⟩

theorem nonempty_rslice_iso (𝓛 M : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty ((Scheme.Modules.pullback (rslice f y)).obj
        (mumfordBundle f L 𝓛 ⊗ (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M)) ≅
      ((Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) ⊗ Scheme.Modules.dual M) := by
  obtain ⟨e1⟩ := nonempty_rslice_mumfordBundle_iso f L 𝓛 h𝓛 y
  have e2 : (Scheme.Modules.pullback (rslice f y)).obj
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M)) ≅ Scheme.Modules.dual M :=
    (pullbackCompIso' (rslice f y) (pullback.fst f f) (𝟙 A) (rslice_fst f y) _).symm ≪≫
      (Scheme.Modules.pullbackId A).app _
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (whiskerRightIso e1 _) ≪≫ whiskerLeftIso _ e2⟩

theorem nonempty_lslice_iso (hc : L.IsCommutative) (𝓛 M : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hM : Scheme.Modules.IsInvertible M) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty ((Scheme.Modules.pullback (lslice f y)).obj
        (mumfordBundle f L 𝓛 ⊗ (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M)) ≅
      (Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by
  obtain ⟨e1⟩ := nonempty_pullback_leftSlice_mumfordBundle_iso_pullback_translate_tensor_dual k f L hc 𝓛 h𝓛 y
  obtain ⟨e3⟩ := Scheme.Modules.nonempty_pullback_comp_point_iso_unit f y.1
    (by rw [y.2]) (Scheme.Modules.dual M) (hM.dual_monoidalV2).1
  have e2 : (Scheme.Modules.pullback (lslice f y)).obj
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M)) ≅ 𝟙_ A.Modules :=
    (pullbackCompIso' (lslice f y) (pullback.fst f f) (f ≫ y.1) (lslice_fst f y) _).symm ≪≫ e3
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (whiskerRightIso e1 _) ≪≫ whiskerLeftIso _ e2 ≪≫ ρ_ _⟩

end Slices

section Points

variable {k : Type} [Field k]

noncomputable def resEquiv (k : Type) [Field k] : k ≃+* IsLocalRing.ResidueField k :=
  RingEquiv.ofBijective (IsLocalRing.residue k)
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr (IsLocalRing.ker_residue.trans IsLocalRing.maximalIdeal_eq_bot),
      IsLocalRing.residue_surjective⟩

theorem exists_algHom_of_isMaximal [IsAlgClosed k] {B : Type} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (𝔪 : Ideal B) [𝔪.IsMaximal] : ∃ χ : B →ₐ[k] k, ∀ b : B, b ∈ 𝔪 ↔ χ b = 0 := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField k) := IsAlgClosed.of_ringEquiv k _ (resEquiv k)
  obtain ⟨ψ, hψ⟩ := IsLocalRing.exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType (A := k) 𝔪
    (by rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]; exact bot_le)
  let χ : B →ₐ[k] k :=
    { toRingHom := (resEquiv k).symm.toRingHom.comp ψ.toRingHom
      commutes' := fun a => by
        change (resEquiv k).symm (ψ (algebraMap k B a)) = a
        rw [ψ.commutes, IsLocalRing.ResidueField.algebraMap_eq]
        exact (resEquiv k).symm_apply_apply a }
  refine ⟨χ, fun b => ?_⟩
  change b ∈ 𝔪 ↔ (resEquiv k).symm (ψ b) = 0
  rw [← hψ, RingHom.mem_ker, map_eq_zero_iff _ (resEquiv k).symm.injective]
  rfl

variable {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

noncomputable def pt (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : A := y.1.base default

theorem range_eq_pt (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Set.range y.1.base = {pt f y} := Set.range_unique

theorem isClosed_pt [IsSeparated f] (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    IsClosed ({pt f y} : Set A) := by
  have : IsClosedImmersion (y.1 ≫ f) := by rw [y.2]; infer_instance
  haveI : IsClosedImmersion y.1 := IsClosedImmersion.of_comp y.1 f
  rw [← range_eq_pt]
  exact y.1.isClosedEmbedding.isClosed_range

noncomputable def ptOfAlgHom (V : A.Opens) (hV : IsAffineOpen V)
    (χ : letI := algebraOfHom f V; Γ(A, V) →ₐ[k] k) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
  letI := algebraOfHom f V
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hV.fromSpec, by
    rw [Category.assoc, fromSpec_comp_eq_specMap f V hV, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show χ.toRingHom.comp (algebraMap k Γ(A, V)) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
      CommRingCat.ofHom_id, Spec.map_id]⟩

theorem pt_ptOfAlgHom_mem (V : A.Opens) (hV : IsAffineOpen V)
    (χ : letI := algebraOfHom f V; Γ(A, V) →ₐ[k] k) : pt f (ptOfAlgHom f V hV χ) ∈ (V : Set A) := by
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

end Points

section Engine

variable {k : Type} [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

noncomputable def gV (V : A.Opens) (hV : IsAffineOpen V) :
    letI := algebraOfHom f V
    pullback f (specMap k Γ(A, V)) ⟶ pullback f f :=
  letI := algebraOfHom f V
  pullback.lift (pullback.fst f (specMap k Γ(A, V))) (pullback.snd f (specMap k Γ(A, V)) ≫ hV.fromSpec)
    (by rw [Category.assoc, fromSpec_comp_eq_specMap f V hV]; exact pullback.condition)

omit [IsAlgClosed k] in
theorem gV_isOpenImmersion_and_range (V : A.Opens) (hV : IsAffineOpen V) :
    letI := algebraOfHom f V
    IsOpenImmersion (gV f V hV) ∧
      Set.range (gV f V hV).base = (((pullback.snd f f) ⁻¹ᵁ V : (pullback f f).Opens) : Set ↑(pullback f f)) := by
  letI := algebraOfHom f V
  obtain ⟨g', hpb, hfst⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom f f V hV
  have hg' : g' = gV f V hV := by
    apply pullback.hom_ext
    · rw [hfst, gV, pullback.lift_fst]
    · rw [gV, pullback.lift_snd]; exact hpb.w
  rw [← hg']
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance, ?_⟩
  have hs : Function.Surjective hpb.isoPullback.hom := hpb.isoPullback.hom.homeomorph.surjective
  rw [← hpb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hs, Set.image_univ]
  change Set.range (pullback.fst (pullback.snd f f) hV.fromSpec).base = _
  rw [IsOpenImmersion.range_pullbackFst, IsAffineOpen.opensRange_fromSpec]

theorem engine [IsProper f] (𝒰A : A.OrderedAffineCover) (N : (pullback f f).Modules) (hN : Scheme.Modules.IsInvertible N)
    (V : A.Opens) (hV : IsAffineOpen V)
    (hfib : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, pt f y ∈ (V : Set A) →
      ∃ X : A.Modules, Scheme.Modules.IsInvertible X ∧
        ((ofModules f X).H0 𝒰A = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules f X).HSucc 𝒰A j)) ∧
        Nonempty ((Scheme.Modules.pullback (rslice f y)).obj N ≅ X)) :
    letI := algebraOfHom f V
    (ofModules (pullback.snd f (specMap k Γ(A, V))) ((Scheme.Modules.pullback (gV f V hV)).obj N)).H0
        (𝒰A.baseChange f Γ(A, V)) = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules (pullback.snd f (specMap k Γ(A, V)))
        ((Scheme.Modules.pullback (gV f V hV)).obj N)).HSucc (𝒰A.baseChange f Γ(A, V)) j) := by
  letI := algebraOfHom f V
  haveI : Algebra.FiniteType k Γ(A, V) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom f V hV
  haveI : IsNoetherianRing Γ(A, V) := Algebra.FiniteType.isNoetherianRing k _
  have hNV : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (gV f V hV)).obj N) := hN.pullback _
  refine OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
    (pullback.snd f (specMap k Γ(A, V))) (𝒰A.baseChange f Γ(A, V)) (fun i s => flat_baseChange_inter f 𝒰A Γ(A, V) i s)
    _ hNV (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial _ _ hNV.exists_trivialization _) ?_
  intro 𝔪 h𝔪
  haveI := h𝔪
  obtain ⟨χ, hχ⟩ := exists_algHom_of_isMaximal (k := k) 𝔪

  obtain ⟨X, hX, hvan, ⟨eX⟩⟩ := hfib (ptOfAlgHom f V hV χ) (pt_ptOfAlgHom_mem f V hV χ)

  obtain ⟨Φ, hΦ, -, -, -, hmod⟩ := P6w f Γ(A, V) hV.fromSpec (specMap k Γ(A, V)) (fromSpec_comp_eq_specMap f V hV)
    rfl 𝔪 χ hχ
  haveI := hΦ
  obtain ⟨eΦ⟩ := hmod N
  exact van_transfer _ f (inv Φ) X hX _ (isoPullbackInv Φ _ X (eΦ ≪≫ eX)) 𝒰A hvan _

end Engine

section Restrict

theorem van_restrict {R R' : Type u} [CommRing R] [CommRing R'] {P Q : Scheme.{u}}
    (π : P ⟶ Spec (.of R)) (ϖ : Q ⟶ Spec (.of R')) [IsSeparated ϖ] (g : Q ⟶ P) [IsOpenImmersion g]
    (U : P.Opens) (hU : Set.range g.base = (U : Set P)) (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝔚Q : Q.OrderedAffineCover)
    (h : (ofModules ϖ ((Scheme.Modules.pullback g).obj N)).H0 𝔚Q = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules ϖ ((Scheme.Modules.pullback g).obj N)).HSucc 𝔚Q j))
    (𝔚 : (U : Scheme.{u}).OrderedAffineCover) :
    (ofModules (U.ι ≫ π) (N.restrict U.ι)).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules (U.ι ≫ π) (N.restrict U.ι)).HSucc 𝔚 j) := by
  let e : (U : Scheme.{u}) ≅ Q := IsOpenImmersion.isoOfRangeEq U.ι g (by rw [Scheme.Opens.range_ι, hU])
  have he : e.hom ≫ g = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have em : N.restrict U.ι ≅ (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback g).obj N) :=
    restrictIsoPullback N U.ι ≪≫ pullbackCompIso' e.hom g U.ι he N
  exact van_transfer (U.ι ≫ π) ϖ e.hom _ (hN.pullback g) _ em 𝔚Q h 𝔚

theorem exists_van_restrict {R R' : Type u} [CommRing R] [CommRing R'] {P Q : Scheme.{u}}
    (π : P ⟶ Spec (.of R)) (ϖ : Q ⟶ Spec (.of R')) [IsSeparated ϖ] (g : Q ⟶ P) [IsOpenImmersion g]
    (U : P.Opens) (hU : Set.range g.base = (U : Set P)) (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝔚Q : Q.OrderedAffineCover)
    (h : (ofModules ϖ ((Scheme.Modules.pullback g).obj N)).H0 𝔚Q = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules ϖ ((Scheme.Modules.pullback g).obj N)).HSucc 𝔚Q j)) :
    ∃ 𝔚 : (U : Scheme.{u}).OrderedAffineCover, (ofModules (U.ι ≫ π) (N.restrict U.ι)).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules (U.ι ≫ π) (N.restrict U.ι)).HSucc 𝔚 j) := by
  let e : (U : Scheme.{u}) ≅ Q := IsOpenImmersion.isoOfRangeEq U.ι g (by rw [Scheme.Opens.range_ι, hU])
  exact ⟨coverComap e.hom 𝔚Q, van_restrict π ϖ g U hU N hN 𝔚Q h _⟩

theorem van_of_restrict {R R' : Type u} [CommRing R] [CommRing R'] {P Q : Scheme.{u}}
    (π : P ⟶ Spec (.of R)) [IsSeparated π] (ϖ : Q ⟶ Spec (.of R')) (g : Q ⟶ P) [IsOpenImmersion g]
    (U : P.Opens) (hU : Set.range g.base = (U : Set P)) (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (h : ∀ 𝔚 : (U : Scheme.{u}).OrderedAffineCover, (ofModules (U.ι ≫ π) (N.restrict U.ι)).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules (U.ι ≫ π) (N.restrict U.ι)).HSucc 𝔚 j))
    (𝔚Q : Q.OrderedAffineCover) :
    (ofModules ϖ ((Scheme.Modules.pullback g).obj N)).H0 𝔚Q = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules ϖ ((Scheme.Modules.pullback g).obj N)).HSucc 𝔚Q j) := by
  let e : (U : Scheme.{u}) ≅ Q := IsOpenImmersion.isoOfRangeEq U.ι g (by rw [Scheme.Opens.range_ι, hU])
  have he : e.inv ≫ U.ι = g := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have em : (Scheme.Modules.pullback g).obj N ≅ (Scheme.Modules.pullback e.inv).obj (N.restrict U.ι) :=
    pullbackCompIso' e.inv U.ι g he N ≪≫ (Scheme.Modules.pullback e.inv).mapIso (restrictIsoPullback N U.ι).symm
  haveI : IsSeparated (U.ι ≫ π) := inferInstance
  exact van_transfer ϖ (U.ι ≫ π) e.inv _ (isInvertible_of_iso (restrictIsoPullback N U.ι).symm (hN.pullback _)) _ em
    (coverComap e.hom 𝔚Q) (h _) 𝔚Q

end Restrict

end L4Asm

p2m_open "AlgebraicGeometry.OModulePresheaf~tensor~ker" in open L4Asm _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : (kernelPts f L 𝓛).Finite)
    (M : A.Modules) (hM : InPicZero f L M) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty (M ⊗ 𝓛 ≅ (Scheme.Modules.pullback (L.translate x)).obj 𝓛) := by
  classical
  by_contra hneg
  rw [not_exists] at hneg
  haveI hPr : IsProper f := hA.proper

  haveI : CompactSpace ↑A := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨𝒰A⟩ := nonempty_orderedAffineCover A
  haveI : CompactSpace ↑(pullback f f) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f ≫ f)
  obtain ⟨𝔛⟩ := nonempty_orderedAffineCover (pullback f f)
  have hAA : ∀ i j, IsAffineOpen (𝒰A.U i ⊓ 𝒰A.U j) := fun i j =>
    Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated f (𝒰A.isAffineOpen i) (𝒰A.isAffineOpen j)

  have hMi : Scheme.Modules.IsInvertible M := hM.1
  have hMd : Scheme.Modules.IsInvertible (Scheme.Modules.dual M) := (hMi.dual_monoidalV2).1
  have h𝓛d : Scheme.Modules.IsInvertible (Scheme.Modules.dual 𝓛) := (h𝓛.dual_monoidalV2).1
  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) :=
    (h𝓛.pullback _).tensor_monoidalV2 ((h𝓛d.pullback _).tensor_monoidalV2 (h𝓛d.pullback _))

  obtain ⟨N₀, ⟨eN₀⟩⟩ : ∃ N₀ : (pullback f f).Modules,
      Nonempty (N₀ ≅ mumfordBundle f L 𝓛 ⊗ (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M)) :=
    ⟨_, ⟨Iso.refl _⟩⟩
  have hN₀ : Scheme.Modules.IsInvertible N₀ := isInvertible_of_iso eN₀.symm (hΛ.tensor_monoidalV2 (hMd.pullback _))

  have hR₀ : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, pt f y ∈ ((⊤ : A.Opens) : Set A) →
      ∃ X : A.Modules, Scheme.Modules.IsInvertible X ∧
        ((ofModules f X).H0 𝒰A = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules f X).HSucc 𝒰A j)) ∧
        Nonempty ((Scheme.Modules.pullback (rslice f y)).obj N₀ ≅ X) := by
    intro y _
    obtain ⟨e1⟩ := nonempty_rslice_iso f L 𝓛 M h𝓛 y
    have hPic : InPicZero f L (((Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) ⊗
        Scheme.Modules.dual M) :=
      InPicZero.tensor k f L (inPicZero_pullback_translate_tensor_dual k f L hc hA 𝓛 h𝓛 y) (InPicZero.dual k f L hM)
    have hne : ¬ Nonempty ((((Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) ⊗
        Scheme.Modules.dual M) ≅ 𝟙_ A.Modules) := by
      rintro ⟨e⟩
      exact hneg y ⟨isoOfTensorDualTensorDualIsoUnit _ 𝓛 M h𝓛 hMi e⟩
    exact ⟨_, hPic.1, H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit k f L hc hA _ hPic hne 𝒰A,
      ⟨(Scheme.Modules.pullback (rslice f y)).mapIso eN₀ ≪≫ e1⟩⟩

  have hVanP : ∀ 𝔚 : (pullback f f).OrderedAffineCover, (ofModules (pullback.fst f f ≫ f) N₀).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules (pullback.fst f f ≫ f) N₀).HSucc 𝔚 j) := by
    refine OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
      (pullback.fst f f ≫ f) (pullback.snd f f) 𝒰A hAA N₀
      (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _ hN₀.exists_trivialization) ?_
    intro i s
    have hW : IsAffineOpen (𝒰A.inter s) := 𝒰A.isAffineOpen_inter f s
    have hg := gV_isOpenImmersion_and_range f (𝒰A.inter s) hW
    haveI := hg.1
    exact exists_van_restrict (pullback.fst f f ≫ f) _ (gV f (𝒰A.inter s) hW) _ hg.2 N₀ hN₀ _
      (engine f 𝒰A N₀ hN₀ (𝒰A.inter s) hW (fun y _ => hR₀ y trivial))

  obtain ⟨N₁, ⟨eN₁⟩⟩ : ∃ N₁ : (pullback f f).Modules,
      Nonempty (N₁ ≅ (Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj N₀) := ⟨_, ⟨Iso.refl _⟩⟩
  have hN₁ : Scheme.Modules.IsInvertible N₁ := isInvertible_of_iso eN₁.symm (hN₀.pullback _)
  have hVanP₁ : ∀ 𝔚 : (pullback f f).OrderedAffineCover, (ofModules (pullback.fst f f ≫ f) N₁).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules (pullback.fst f f ≫ f) N₁).HSucc 𝔚 j) := fun 𝔚 =>
    van_transfer (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) (pullbackSymmetry f f).hom N₀ hN₀ N₁ eN₁ 𝔛 (hVanP 𝔛) 𝔚
  have hR₁ : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty ((Scheme.Modules.pullback (rslice f y)).obj N₁ ≅
        (Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by
    intro y
    obtain ⟨e1⟩ := nonempty_lslice_iso f L hc 𝓛 M h𝓛 hMi y
    exact ⟨(Scheme.Modules.pullback (rslice f y)).mapIso eN₁ ≪≫
      (pullbackCompIso' (rslice f y) (pullbackSymmetry f f).hom (lslice f y) (rslice_symmetry f y) N₀).symm ≪≫
      (Scheme.Modules.pullback (lslice f y)).mapIso eN₀ ≪≫ e1⟩
  have hY : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, y ∉ kernelPts f L 𝓛 →
      ∃ X : A.Modules, Scheme.Modules.IsInvertible X ∧
        ((ofModules f X).H0 𝒰A = ⊥ ∧ ∀ j : ℕ, Subsingleton ((ofModules f X).HSucc 𝒰A j)) ∧
        Nonempty ((Scheme.Modules.pullback (rslice f y)).obj N₁ ≅ X) := by
    intro y hy
    have hPic := inPicZero_pullback_translate_tensor_dual k f L hc hA 𝓛 h𝓛 y
    have hne : ¬ Nonempty (((Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) ≅ 𝟙_ A.Modules) := by
      rintro ⟨e⟩
      exact hy ((mem_kernelPts_iff_nonempty_pullback_translate_iso k f L 𝓛 y).mpr ⟨isoOfTensorDualIsoUnit _ 𝓛 h𝓛 e⟩)
    exact ⟨_, hPic.1, H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit k f L hc hA _ hPic hne 𝒰A, hR₁ y⟩

  let e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := L.one (𝟙 _)
  obtain ⟨S, hS⟩ : ∃ S : Set A, S = (pt f '' kernelPts f L 𝓛) \ {pt f e₀} := ⟨_, rfl⟩
  have hSfin : S.Finite := by rw [hS]; exact (hK.image _).diff
  have hScl : ∀ s ∈ S, IsClosed ({s} : Set A) := by
    rw [hS]; rintro s ⟨⟨y, -, rfl⟩, -⟩; exact isClosed_pt f y
  obtain ⟨V, hV, heV, hVS⟩ := Scheme.exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed S hSfin hScl (pt f e₀)
    (by rw [hS]; exact fun h => h.2 rfl)
  let O : A.Opens := ⟨{pt f e₀}ᶜ, (isClosed_pt f e₀).isOpen_compl⟩
  have hOV : O ⊔ V = ⊤ := by
    refine top_le_iff.mp fun a _ => TopologicalSpace.Opens.mem_sup.mpr ?_
    by_cases ha : a = pt f e₀
    · exact Or.inr (ha ▸ heV)
    · exact Or.inl ha
  have hkey : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      pt f y ∈ ((O ⊓ V : A.Opens) : Set A) → y ∉ kernelPts f L 𝓛 := by
    intro y h1 h3
    exact (Set.disjoint_left.mp hVS) h1.2 (hS ▸ ⟨⟨y, h3, rfl⟩, h1.1⟩)

  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherian A := {}
  haveI : CompactSpace ↑((O ⊓ V : A.Opens) : Scheme.{0}) :=
    (inferInstance : TopologicalSpace.NoetherianSpace ((O ⊓ V : A.Opens) : Set A)).compactSpace
  obtain ⟨𝒱⟩ := nonempty_orderedAffineCover ((O ⊓ V : A.Opens) : Scheme.{0})
  haveI : IsSeparated ((O ⊓ V).ι ≫ f) := inferInstance
  have hVVV : ∀ i j, IsAffineOpen (𝒱.U i ⊓ 𝒱.U j) := fun i j =>
    Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated ((O ⊓ V).ι ≫ f) (𝒱.isAffineOpen i) (𝒱.isAffineOpen j)

  set q := pullback.snd f f with hq
  set πP := pullback.fst f f ≫ f with hπP
  have hN₁q : (ofModules πP N₁).IsQuasicoherent :=
    OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _ hN₁.exists_trivialization
  have hW : ∀ 𝔚 : ((q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V : (pullback f f).Opens) : Scheme.{0}).OrderedAffineCover,
      (ofModules ((q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V).ι ≫ πP) (N₁.restrict (q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V).ι)).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules ((q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V).ι ≫ πP) (N₁.restrict (q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V).ι)).HSucc 𝔚 j) := by
    change ∀ 𝔚 : ((q ⁻¹ᵁ (O ⊓ V) : (pullback f f).Opens) : Scheme.{0}).OrderedAffineCover,
      (ofModules ((q ⁻¹ᵁ (O ⊓ V)).ι ≫ πP) (N₁.restrict (q ⁻¹ᵁ (O ⊓ V)).ι)).H0 𝔚 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules ((q ⁻¹ᵁ (O ⊓ V)).ι ≫ πP) (N₁.restrict (q ⁻¹ᵁ (O ⊓ V)).ι)).HSucc 𝔚 j)
    have hN₁r : Scheme.Modules.IsInvertible (N₁.restrict (q ⁻¹ᵁ (O ⊓ V)).ι) :=
      isInvertible_of_iso (restrictIsoPullback N₁ _).symm (hN₁.pullback _)
    haveI : IsSeparated ((q ⁻¹ᵁ (O ⊓ V)).ι ≫ πP) := inferInstance
    refine OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
      ((q ⁻¹ᵁ (O ⊓ V)).ι ≫ πP) (q ∣_ (O ⊓ V)) 𝒱 hVVV _
      (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _ hN₁r.exists_trivialization) ?_
    intro i s
    have hW' : IsAffineOpen (𝒱.inter s) := 𝒱.isAffineOpen_inter ((O ⊓ V).ι ≫ f) s
    have hWA : IsAffineOpen ((O ⊓ V).ι ''ᵁ 𝒱.inter s) := hW'.image_of_isOpenImmersion _
    letI := algebraOfHom f ((O ⊓ V).ι ''ᵁ 𝒱.inter s)
    have hsub : (((O ⊓ V).ι ''ᵁ 𝒱.inter s : A.Opens) : Set A) ⊆ ((O ⊓ V : A.Opens) : Set A) :=
      Scheme.Opens.ι_image_le _ _

    have hE := engine f 𝒰A N₁ hN₁ _ hWA (fun y hy => hY y (hkey y (hsub hy)))
    have hg := gV_isOpenImmersion_and_range f _ hWA
    haveI := hg.1

    have hrange : Set.range (gV f _ hWA).base ⊆ Set.range (q ⁻¹ᵁ (O ⊓ V)).ι.base := by
      rw [hg.2, Scheme.Opens.range_ι]
      exact fun p hp => hsub hp
    let g' := IsOpenImmersion.lift (q ⁻¹ᵁ (O ⊓ V)).ι (gV f _ hWA) hrange
    have hg' : g' ≫ (q ⁻¹ᵁ (O ⊓ V)).ι = gV f _ hWA := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion g' := by
      have : IsOpenImmersion (g' ≫ (q ⁻¹ᵁ (O ⊓ V)).ι) := by rw [hg']; infer_instance
      exact IsOpenImmersion.of_comp g' (q ⁻¹ᵁ (O ⊓ V)).ι
    have hg'range : Set.range g'.base = (((q ∣_ (O ⊓ V)) ⁻¹ᵁ 𝒱.inter s :
        (↑(q ⁻¹ᵁ (O ⊓ V)) : Scheme.{0}).Opens) : Set ↑(q ⁻¹ᵁ (O ⊓ V))) := by
      apply (Scheme.Opens.ι _).isOpenEmbedding.injective.image_injective
      rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hg', hg.2,
        ← Scheme.Hom.coe_image, image_morphismRestrict_preimage]
    refine exists_van_restrict ((q ⁻¹ᵁ (O ⊓ V)).ι ≫ πP) (pullback.snd f (specMap k Γ(A, (O ⊓ V).ι ''ᵁ 𝒱.inter s)))
      g' _ hg'range _ hN₁r (𝒰A.baseChange f _) ?_
    have em : (Scheme.Modules.pullback g').obj (N₁.restrict (q ⁻¹ᵁ (O ⊓ V)).ι) ≅
        (Scheme.Modules.pullback (gV f _ hWA)).obj N₁ :=
      (Scheme.Modules.pullback g').mapIso (restrictIsoPullback N₁ _) ≪≫ (pullbackCompIso' g' _ _ hg' N₁).symm
    exact (van_iff_of_iso _ em _).mpr hE

  have hUV : q ⁻¹ᵁ O ⊔ q ⁻¹ᵁ V = ⊤ := by rw [← Scheme.Hom.preimage_sup, hOV]; rfl
  have hVg := gV_isOpenImmersion_and_range f V hV
  haveI := hVg.1
  letI := algebraOfHom f V
  obtain ⟨𝔚OV⟩ : Nonempty (((q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V : (pullback f f).Opens) : Scheme.{0}).OrderedAffineCover) := by
    haveI : IsLocallyNoetherian ↑(pullback f f) := LocallyOfFiniteType.isLocallyNoetherian πP
    haveI : IsNoetherian ↑(pullback f f) := {}
    haveI : CompactSpace ↑((q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V : (pullback f f).Opens) : Scheme.{0}) :=
      (inferInstance : TopologicalSpace.NoetherianSpace ((q ⁻¹ᵁ O ⊓ q ⁻¹ᵁ V : (pullback f f).Opens) : Set ↑(pullback f f))).compactSpace
    exact nonempty_orderedAffineCover _
  have hExc : ∀ 𝔙 : ((q ⁻¹ᵁ V : (pullback f f).Opens) : Scheme.{0}).OrderedAffineCover,
      (ofModules ((q ⁻¹ᵁ V).ι ≫ πP) (N₁.restrict (q ⁻¹ᵁ V).ι)).H0 𝔙 = ⊥ ∧
      ∀ j : ℕ, Subsingleton ((ofModules ((q ⁻¹ᵁ V).ι ≫ πP) (N₁.restrict (q ⁻¹ᵁ V).ι)).HSucc 𝔙 j) := fun 𝔙 =>
    OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top πP N₁ hN₁q (q ⁻¹ᵁ O) (q ⁻¹ᵁ V) hUV 𝔛 𝔙 𝔚OV
      (hVanP₁ 𝔛) (hW 𝔚OV)

  have hPV := van_of_restrict πP (pullback.snd f (specMap k Γ(A, V))) (gV f V hV) (q ⁻¹ᵁ V) hVg.2 N₁ hN₁ hExc
    (𝒰A.baseChange f Γ(A, V))

  have hrng : Set.range e₀.1.base ⊆ Set.range hV.fromSpec.base := by
    rw [range_eq_pt, IsAffineOpen.range_fromSpec]; exact Set.singleton_subset_iff.mpr heV
  let ℓ := IsOpenImmersion.lift hV.fromSpec e₀.1 hrng
  have hℓ : ℓ ≫ hV.fromSpec = e₀.1 := IsOpenImmersion.lift_fac _ _ _
  let φ := Spec.preimage ℓ
  have hφ : Spec.map φ = ℓ := Spec.map_preimage ℓ
  have hφalg : ∀ a : k, φ.hom (algebraMap k Γ(A, V) a) = a := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap k Γ(A, V)) ≫ φ) = 𝟙 _ := by
      rw [Spec.map_comp, hφ, show Spec.map (CommRingCat.ofHom (algebraMap k Γ(A, V))) = specMap k Γ(A, V) from rfl,
        ← fromSpec_comp_eq_specMap f V hV, ← Category.assoc, hℓ]
      exact e₀.2
    have h2 : CommRingCat.ofHom (algebraMap k Γ(A, V)) ≫ φ = 𝟙 _ := Spec.map_injective (by rw [h1, Spec.map_id])
    intro a
    exact congrArg (fun ψ : CommRingCat.of k ⟶ CommRingCat.of k => ψ.hom a) h2
  let χ : Γ(A, V) →ₐ[k] k := { toRingHom := φ.hom, commutes' := hφalg }
  let 𝔪 : Ideal Γ(A, V) := RingHom.ker χ.toRingHom
  have hχ : ∀ b, b ∈ 𝔪 ↔ χ b = 0 := fun b => RingHom.mem_ker
  haveI : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective χ.toRingHom
    (fun a => ⟨algebraMap k Γ(A, V) a, hφalg a⟩)
  have hχe : Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hV.fromSpec = e₀.1 := by
    rw [show CommRingCat.ofHom χ.toRingHom = φ from rfl, hφ, hℓ]

  have hBF := OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
    (pullback.snd f (specMap k Γ(A, V))) (𝒰A.baseChange f Γ(A, V)) (fun i s => flat_baseChange_inter f 𝒰A Γ(A, V) i s)
    _ (hN₁.pullback _) hPV.1 hPV.2 (Γ(A, V) ⧸ 𝔪)

  obtain ⟨Φ, hΦ, -, -, -, hmod⟩ := P6w f Γ(A, V) hV.fromSpec (specMap k Γ(A, V)) (fromSpec_comp_eq_specMap f V hV)
    rfl 𝔪 χ hχ
  haveI := hΦ
  obtain ⟨eΦ⟩ := hmod N₁
  have hsl : rslice f (ptOfAlgHom f V hV χ) = rslice f e₀ := by
    apply pullback.hom_ext
    · rw [rslice_fst, rslice_fst]
    · rw [rslice_snd, rslice_snd]
      exact congrArg (f ≫ ·) hχe
  obtain ⟨eY⟩ := hR₁ e₀
  have eT : (Scheme.Modules.pullback (L.translate e₀)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅ 𝟙_ A.Modules :=
    whiskerRightIso ((Scheme.Modules.pullbackCongr (L.translate_one)).app 𝓛 ≪≫ (Scheme.Modules.pullbackId A).app 𝓛) _ ≪≫
      (h𝓛.dual_monoidalV2).2.some
  have e1 : 𝟙_ A.Modules ≅ (Scheme.Modules.pullback Φ).obj
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (specMap k Γ(A, V))) (specMap Γ(A, V) (Γ(A, V) ⧸ 𝔪)))).obj
        ((Scheme.Modules.pullback (gV f V hV)).obj N₁)) :=
    (eΦ ≪≫ (Scheme.Modules.pullbackCongr hsl).app N₁ ≪≫ eY ≪≫ eT).symm
  have hfin := van_transfer f _ Φ _ ((hN₁.pullback _).pullback _) (𝟙_ A.Modules) e1 _ hBF 𝒰A

  obtain ⟨⟨u0⟩, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_tensorUnit_unit f 𝒰A
  have h1 := GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one k f hA 𝒰A
  rw [OModulePresheaf.cechFinrank_zero, ← u0.finrank_eq, hfin.1, finrank_bot] at h1
  exact zero_ne_one h1

end S_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite (solution)
