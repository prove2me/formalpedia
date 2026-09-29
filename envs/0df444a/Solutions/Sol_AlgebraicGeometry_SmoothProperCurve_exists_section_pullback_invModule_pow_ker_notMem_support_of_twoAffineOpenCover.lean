-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0f5f67a0-b6d4-51f1-961a-58647b647356

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover.AlgebraicGeometry AlgebraicCurve NeronModelInfra AlgebraicGeometry.RelPicard Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.id_app Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.IdealSheafData.IsInvertible SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso RelPicard.nonempty_pullback_sectionTwist_iso Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker"
namespace FibreNonvanishAux
p2m_open "AlgebraicGeometry.SmoothProperCurve~specMap AlgebraicGeometry"

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (.of K))

noncomputable def appTopLinear {M N : X.Modules} (φ : M ⟶ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
    Γ(M, ⊤) →ₗ[K] Γ(N, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
  { toFun := fun v => φ.app ⊤ v
    map_add' := fun a b => map_add _ a b
    map_smul' := fun k v => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom x (⊤ : X.Opens)
      show φ.app ⊤ ((algebraMap K Γ(X, ⊤) k) • v) = (algebraMap K Γ(X, ⊤) k) • φ.app ⊤ v
      exact Scheme.Modules.Hom.app_smul φ _ v }

theorem appTopLinear_apply {M N : X.Modules} (φ : M ⟶ N) (v : Γ(M, ⊤)) :
    appTopLinear x φ v = φ.app ⊤ v := rfl

noncomputable def isoSections {M N : X.Modules} (e : M ≅ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
    Γ(M, ⊤) ≃ₗ[K] Γ(N, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
  { appTopLinear x e.hom with
    invFun := appTopLinear x e.inv
    left_inv := fun v => by
      show e.inv.app ⊤ (e.hom.app ⊤ v) = v
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    right_inv := fun v => by
      show e.hom.app ⊤ (e.inv.app ⊤ v) = v
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] }

theorem exists_hom_app_top_eq (N : X.Modules) (v : Γ(N, ⊤)) :
    ∃ s : 𝟙_ X.Modules ⟶ N, s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = v := by
  let sec : N.val.sections :=
    PresheafOfModules.sectionsMk (M := N.val) (fun U => N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op v)
      (by
        intro U V f
        show (N.presheaf ⋙ forget _).map f (N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op v) =
          N.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op v
        have hf : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
          Quiver.Hom.unop_inj (Subsingleton.elim _ _)
        rw [← hf, Functor.map_comp]
        rfl)
  refine ⟨N.unitHomEquiv.symm sec, ?_⟩
  have h1 := SheafOfModules.unitHomEquiv_apply_coe N (N.unitHomEquiv.symm sec) (op ⊤)
  rw [Equiv.apply_symm_apply] at h1

  have h2 : sec.val (op ⊤) = v := by
    show N.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op v = v
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  rw [← h2, h1]
  rfl

end AlgebraicGeometry.SmoothProperCurve.FibreNonvanishAux

open AlgebraicGeometry.SmoothProperCurve.FibreNonvanishAux

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (m : ℕ) (hm : 2 * g ≤ m) (hm₁ : 1 ≤ m) (𝒱 : C.TwoAffineOpenCover)
    (K : Type u) [Field K] [Algebra R K] :
    ∃ s : 𝟙_ (pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Modules ⟶
        (Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj
          ((ε.1.ker ^ m).invModule),
      ∀ z : Spec (CommRingCat.of K) ⟶ pullback c (Scheme.TwoAffineOpenCover.specMap R K),
        z ≫ pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K) =
            Scheme.TwoAffineOpenCover.specMap R K ≫ ε.1 →
        z ≫ pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K) = 𝟙 _ →
        z.base (IsLocalRing.closedPoint K) ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by

  let S : Scheme.{u} := Spec (CommRingCat.of R)
  let sK : Spec (CommRingCat.of K) ⟶ S := Scheme.TwoAffineOpenCover.specMap R K
  let xK : pullback c sK ⟶ Spec (CommRingCat.of K) := pullback.snd c sK
  let F : pullback c sK ⟶ C := pullback.fst c sK
  let σ : Spec (CommRingCat.of K) ⟶ pullback c sK := rigSection c sK ε
  have hσx : σ ≫ xK = 𝟙 _ := by simp only [σ, xK, rigSection, pullback.lift_snd]
  have hσF : σ ≫ F = sK ≫ ε.1 := by simp only [σ, F, rigSection, pullback.lift_fst]

  suffices h : ∃ s : 𝟙_ (pullback c sK).Modules ⟶ (Scheme.Modules.pullback F).obj ((ε.1.ker ^ m).invModule),
      σ.base (IsLocalRing.closedPoint K) ∉ (Scheme.Modules.zeroSchemeIdeal s).support by
    obtain ⟨s, hs⟩ := h
    refine ⟨s, fun z hzF hzx => ?_⟩
    have hz : z = σ := pullback.hom_ext (hzF.trans hσF.symm) (hzx.trans hσx.symm)
    rw [hz]
    exact hs

  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩

  have hεc : ε.1 ≫ c = 𝟙 S := ε.2
  haveI : IsClosedImmersion (ε.1 ≫ c) := by rw [hεc]; infer_instance
  haveI : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hIε : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 hεc
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 S)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 xK :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσ1 : rigSection c (𝟙 S) ε ≫ pullback.snd c (𝟙 S) = 𝟙 S := by simp only [rigSection, pullback.lift_snd]
  have hI1 : (rigSection c (𝟙 S) ε).ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (𝟙 S) ε) hσ1
  have hσ1π : rigSection c (𝟙 S) ε ≫ pullback.fst c (𝟙 S) = ε.1 := by
    simp only [rigSection, pullback.lift_fst, Category.id_comp]
  haveI : IsClosedImmersion (σ ≫ xK) := by rw [hσx]; infer_instance
  haveI : IsClosedImmersion σ := IsClosedImmersion.of_comp σ xK
  have hIσ : σ.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ hσx

  let ψ : SchemeHomOver sK (𝟙 S) := ⟨sK, Category.comp_id _⟩
  let g₁ : pullback c sK ⟶ pullback c (𝟙 S) := baseChangeSnd c ψ
  let π : pullback c (𝟙 S) ⟶ C := pullback.fst c (𝟙 S)
  have hg₁π : g₁ ≫ π = F := by
    simp only [g₁, π, F, baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have eT : ∀ r : ℕ, Nonempty ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ r).invModule) ≅ (σ.ker ^ r).invModule) := by
    intro r
    obtain ⟨eπ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso π ε.1
      (rigSection c (𝟙 S) ε) hσ1π hIε hI1 r).1
    obtain ⟨eψ⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ r
    exact ⟨(Scheme.Modules.pullbackCongr hg₁π.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp g₁ π).app _).symm ≪≫
      (Scheme.Modules.pullback g₁).mapIso eπ ≪≫ eψ⟩

  let P : (pullback c sK).Modules := (σ.ker ^ (d + 1)).invModule
  have hP : Scheme.Modules.IsInvertible P := (hIσ.pow (d + 1)).isInvertible_invModule
  let G : (pullback c sK).Modules := 𝟙_ _ ⊗ P
  let Gd : (pullback c sK).Modules := 𝟙_ _ ⊗ (σ.ker ^ d).invModule
  let i := (σ.ker ^ 1).subschemeι
  let η := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G
  obtain ⟨-, ι, w, hSE⟩ :=
    Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact
      σ.ker hIσ (𝟙_ _) (Scheme.Modules.isInvertible_unit _) (d + 1) 1 d rfl
  obtain ⟨em⟩ := eT (d + 1)
  obtain ⟨ed⟩ := eT d
  let θm : (Scheme.Modules.pullback F).obj ((ε.1.ker ^ (d + 1)).invModule) ≅ G := em ≪≫ (λ_ P).symm
  let θd : (Scheme.Modules.pullback F).obj ((ε.1.ker ^ d).invModule) ≅ Gd := ed ≪≫ (λ_ _).symm

  letI iGm := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK G ⊤
  letI iGd := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK Gd ⊤
  letI iFm := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK
    ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ (d + 1)).invModule)) ⊤
  letI iFd := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK
    ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ d).invModule)) ⊤
  have hGm : Module.finrank K Γ(G, ⊤) = d + 1 + 1 - g := by
    obtain ⟨-, h0⟩ :=
      AlgebraicGeometry.SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
        R c ε g hg (d + 1) (by omega) 𝒱 K
    obtain ⟨eH, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 (𝒱.pullback c K) xK
      ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ (d + 1)).invModule))
    rw [← h0, ← eH.finrank_eq, (isoSections xK θm).finrank_eq]
  have hGd : Module.finrank K Γ(Gd, ⊤) = d + 1 - g := by
    obtain ⟨-, h0⟩ :=
      AlgebraicGeometry.SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
        R c ε g hg d (by omega) 𝒱 K
    obtain ⟨eH, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 (𝒱.pullback c K) xK
      ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ d).invModule))
    rw [← h0, ← eH.finrank_eq, (isoSections xK θd).finrank_eq]

  suffices h : ∃ s' : 𝟙_ _ ⟶ G, σ.base (IsLocalRing.closedPoint K) ∉ (Scheme.Modules.zeroSchemeIdeal s').support by
    obtain ⟨s', hs'⟩ := h
    refine ⟨s' ≫ θm.inv, ?_⟩
    rwa [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]
  by_contra hall
  simp only [not_exists, not_not] at hall

  have hτ : σ.ker ≤ i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, pow_one]
  let τ := IsClosedImmersion.lift σ i hτ
  have hτσ : τ ≫ σ = i := IsClosedImmersion.lift_fac σ i hτ
  have hA : ∀ s' : 𝟙_ _ ⟶ G, s' ≫ η = 0 := by
    intro s'

    have hmem := hall s'
    have hZ : Scheme.Modules.zeroSchemeIdeal (s' ≫ (λ_ P).hom) = Scheme.Modules.zeroSchemeIdeal s' :=
      Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso _ _
    rw [← hZ] at hmem
    have h0 : Scheme.Modules.pullbackSection σ (s' ≫ (λ_ P).hom) = 0 :=
      (Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support hP _ σ).mpr hmem
    rw [Scheme.Modules.pullbackSection_def] at h0
    have h1 : (Scheme.Modules.pullback σ).map (s' ≫ (λ_ P).hom) = 0 :=
      (cancel_epi _).mp (h0.trans comp_zero.symm)
    rw [Functor.map_comp] at h1
    have h2 : (Scheme.Modules.pullback σ).map s' = 0 :=
      (cancel_mono _).mp (h1.trans zero_comp.symm)

    have h3 : (Scheme.Modules.pullback (τ ≫ σ)).map s' = 0 := by
      have nat := (Scheme.Modules.pullbackComp τ σ).hom.naturality s'
      have h5 : (Scheme.Modules.pullback τ).map ((Scheme.Modules.pullback σ).map s') = 0 := by
        rw [h2, Functor.map_zero]
      rw [Functor.comp_map, h5] at nat
      have h6 : (Scheme.Modules.pullbackComp τ σ).hom.app _ ≫ (Scheme.Modules.pullback (τ ≫ σ)).map s' = 0 :=
        nat.symm.trans zero_comp
      exact (cancel_epi _).mp (h6.trans comp_zero.symm)
    have h4 : (Scheme.Modules.pullback i).map s' = 0 := by
      have nat := (Scheme.Modules.pullbackCongr hτσ).hom.naturality s'
      rw [h3] at nat
      have h6 : (Scheme.Modules.pullbackCongr hτσ).hom.app _ ≫ (Scheme.Modules.pullback i).map s' = 0 :=
        nat.symm.trans zero_comp
      exact (cancel_epi _).mp (h6.trans comp_zero.symm)

    have nat := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality s'
    have h5 : (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map s') = 0 := by
      rw [h4, Functor.map_zero]
    rw [Functor.comp_map, h5, Functor.id_map] at nat
    exact nat.trans comp_zero

  have hB : ∀ v : Γ(G, ⊤), η.app ⊤ v = 0 := by
    intro v
    obtain ⟨s', hs'⟩ := exists_hom_app_top_eq G v
    rw [← hs']
    have h := congrArg (fun φ => φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) (hA s')
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h
    exact h

  haveI : Mono (ShortComplex.mk ι _ w).f := hSE.mono_f
  have hC : Function.Surjective (appTopLinear xK ι) := by
    intro v
    obtain ⟨e, he⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero (ShortComplex.mk ι _ w) hSE.exact ⊤ v (hB v)
    exact ⟨e, he⟩

  have hpos : 0 < Module.finrank K Γ(Gd, ⊤) := by rw [hGd]; omega
  haveI : Module.Finite K Γ(Gd, ⊤) := Module.finite_of_finrank_pos hpos
  have hle : Module.finrank K Γ(G, ⊤) ≤ Module.finrank K Γ(Gd, ⊤) := by
    have := LinearMap.finrank_range_le (appTopLinear xK ι)
    rwa [LinearMap.range_eq_top.mpr hC, finrank_top] at this
  rw [hGm, hGd] at hle
  omega

end S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover (solution)
