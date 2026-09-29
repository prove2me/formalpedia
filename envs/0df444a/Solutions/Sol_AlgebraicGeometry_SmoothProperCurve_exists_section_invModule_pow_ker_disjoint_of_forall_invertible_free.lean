-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/88d82d43-630c-55e0-bb37-991f02111e04

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_notMem_support_of_isMaximal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free.AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free.AlgebraicGeometry.SmoothProperCurve NeronModelInfra"

p2m_open "CategoryTheory.MonoidalCategory"
open AlgebraicCurve

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Surjective Scheme.IdealSheafData.support_comap Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom.comp_app Scheme.isoSpec_hom Scheme.Modules.Hom Scheme.homeoOfIso Spec Scheme.Hom.id_appTop Scheme Scheme.Hom.appTop Scheme.Hom.comp_appTop Scheme.Modules.Hom.add_app Scheme.zeroLocus_span Scheme.mem_zeroLocus_iff isAffineOpen_top Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules Scheme.toSpecΓ_preimage_basicOpen Scheme.IdealSheafData.mem_support_iff_of_mem toSpecΓ Scheme.IdealSheafData Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_add Scheme.Modules.pullbackLocalSection_zero Scheme.Modules.pullbackLocalSection_smul Scheme.Modules.pullbackLocalSection_app Scheme.Modules.unitSection Scheme.Modules.smul_unitSection Scheme.Modules.isFrameOn_unitSection Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection Scheme.Hom.isInvertible_ker_of_comp_eq_id SmoothProperCurve.exists_section_invModule_pow_ker_notMem_support_of_isMaximal Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "exists_section_invModule_pow_ker_notMem_support_of_isMaximal"
namespace LIFT2Aux
p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

variable {X Y : Scheme.{u}}

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  simpa using ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

lemma hom_ext_of_app_top {N : X.Modules} {f g : 𝟙_ X.Modules ⟶ N}
    (h : f.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = g.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  have hx : x = (Scheme.Modules.ofUnitSection U x) •
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_map,
      Scheme.Modules.ofUnitSection_toUnitSection, map_one, mul_one]
  rw [hx, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_map, app_map, h]

lemma exists_hom_app_top_eq {N : X.Modules} (s₀ : Γ(N, ⊤)) :
    ∃ s : 𝟙_ X.Modules ⟶ N, s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = s₀ := by
  let σ : N.val.sections := PresheafOfModules.sectionsMk
    (fun U => N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s₀)
    (by
      intro U V f
      change N.presheaf.map f (N.presheaf.map _ s₀) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrFun (congrArg (fun j => ⇑(ConcreteCategory.hom (N.presheaf.map j)))
        (Subsingleton.elim _ _)) s₀)
  refine ⟨(SheafOfModules.unitHomEquiv N).symm σ, ?_⟩
  have h := SheafOfModules.unitHomEquiv_apply_coe N ((SheafOfModules.unitHomEquiv N).symm σ)
    (Opposite.op ⊤)
  rw [Equiv.apply_symm_apply] at h
  have h' : σ.val (Opposite.op ⊤) = s₀ := by
    change N.presheaf.map _ s₀ = s₀
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, N.presheaf.map_id]
    rfl
  change ((SheafOfModules.unitHomEquiv N).symm σ).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = s₀
  exact h.symm.trans h'

lemma exists_pullbackSection_eq (F : X ⟶ Y) (M : Y.Modules)
    (hsurj : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction F).unit.app M).app ⊤).hom)
    (t' : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback F).obj M) :
    ∃ s : 𝟙_ Y.Modules ⟶ M, Scheme.Modules.pullbackSection F s = t' := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction F with hadj
  let t : (Scheme.Modules.pullback F).obj (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pullback F).obj M :=
    (Scheme.Modules.pullbackUnitIso F).hom ≫ t'
  let tflat : 𝟙_ Y.Modules ⟶ (Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback F).obj M) :=
    adj.homEquiv _ _ t
  obtain ⟨s₀, hs₀⟩ := hsurj (tflat.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
  obtain ⟨s, hs⟩ := exists_hom_app_top_eq (N := M) s₀
  refine ⟨s, ?_⟩
  have h1 : s ≫ adj.unit.app M = tflat := by
    apply hom_ext_of_app_top
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.ConcreteCategory.comp_apply, hs]
    exact hs₀
  have h2 : adj.homEquiv _ _ ((Scheme.Modules.pullback F).map s) = s ≫ adj.unit.app M := by
    rw [Adjunction.homEquiv_apply]
    exact (adj.unit.naturality s).symm
  have h3 : (Scheme.Modules.pullback F).map s = t := (adj.homEquiv _ _).injective (h2.trans h1)
  rw [Scheme.Modules.pullbackSection_def]
  exact (congrArg (fun φ => (Scheme.Modules.pullbackUnitIso F).inv ≫ φ) h3).trans (by simp [t])

end AlgebraicGeometry.SmoothProperCurve.LIFT2Aux

namespace LComb

variable {X C : Scheme.{u}} (ε : X ⟶ C) {M : C.Modules}
  (e : (Scheme.Modules.pullback ε).obj M ≅ 𝟙_ X.Modules)

noncomputable def cval (s : 𝟙_ C.Modules ⟶ M) : Γ(X, ⊤) :=
  Scheme.Modules.ofUnitSection ⊤
    (e.hom.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection ε (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))))

lemma cval_add (s s' : 𝟙_ C.Modules ⟶ M) : cval ε e (s + s') = cval ε e s + cval ε e s' := by
  unfold cval
  have h1 : (s + s').app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) + s'.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) := by
    rw [Scheme.Modules.Hom.add_app]; rfl
  rw [h1, Scheme.Modules.pullbackLocalSection_add, map_add]
  rfl

lemma cval_smul (g : Γ(C, ⊤)) (s μ : 𝟙_ C.Modules ⟶ M)
    (hμ : μ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = g • s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    cval ε e μ = ε.appTop g * cval ε e s := by
  unfold cval
  rw [hμ, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  rfl

lemma app_pullbackSection_comp (s : 𝟙_ C.Modules ⟶ M) :
    (Scheme.Modules.pullbackSection ε s ≫ e.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      cval ε e s • Scheme.Modules.unitSection ⊤ := by
  rw [Scheme.Modules.smul_unitSection]
  show e.hom.app ⊤ (((Scheme.Modules.pullback ε).map s).app ⊤
    ((Scheme.Modules.pullbackUnitIso ε).inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) = _

  have h1 : (Scheme.Modules.pullbackUnitIso ε).inv.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (ε ⁻¹ᵁ ⊤) 1) =
      Scheme.Modules.pullbackLocalSection ε (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤))) := by
    have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection ε ⊤ (1 : Γ(C, ⊤))
    rw [map_one] at h
    rw [← h]
    change ((Scheme.Modules.pullbackUnitIso ε).hom ≫ (Scheme.Modules.pullbackUnitIso ε).inv).app _ _ = _
    rw [Iso.hom_inv_id]
    rfl
  have h2 : ((Scheme.Modules.pullback ε).map s).app (ε ⁻¹ᵁ ⊤)
      (Scheme.Modules.pullbackLocalSection ε (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤)))) =
      Scheme.Modules.pullbackLocalSection ε (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :=
    (Scheme.Modules.pullbackLocalSection_app ε s _).symm
  change e.hom.app (ε ⁻¹ᵁ ⊤) (((Scheme.Modules.pullback ε).map s).app (ε ⁻¹ᵁ ⊤)
    ((Scheme.Modules.pullbackUnitIso ε).inv.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (ε ⁻¹ᵁ ⊤) 1))) = _
  rw [h1, h2]
  rfl

lemma cval_zero : cval ε e (0 : 𝟙_ C.Modules ⟶ M) = 0 := by
  unfold cval
  have h1 : (0 : 𝟙_ C.Modules ⟶ M).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = 0 := by
    rw [Scheme.Modules.Hom.zero_app]; rfl
  rw [h1, Scheme.Modules.pullbackLocalSection_zero, map_zero]
  rfl

lemma cval_sum {ι : Type*} (S : Finset ι) (s : ι → (𝟙_ C.Modules ⟶ M)) :
    cval ε e (∑ i ∈ S, s i) = ∑ i ∈ S, cval ε e (s i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact cval_zero ε e
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cval_add, ih]

lemma mem_support_iff (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ C.Modules ⟶ M) (p : X) :
    ε.base p ∈ (Scheme.Modules.zeroSchemeIdeal s).support ↔
      p ∈ (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection ε s ≫ e.hom)).support := by
  rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso, ← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal ε hM s,
    Scheme.IdealSheafData.support_comap]
  rfl

lemma mem_support_iff_mem_zeroLocus (hX : IsAffineOpen (⊤ : X.Opens)) (σ : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (cv : Γ(X, ⊤)) (hσ : σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = cv • Scheme.Modules.unitSection ⊤) (p : X) :
    p ∈ (Scheme.Modules.zeroSchemeIdeal σ).support ↔ p ∈ X.zeroLocus ({cv} : Set Γ(X, ⊤)) := by
  have hid := Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
    (Scheme.Modules.isInvertible_unit X) (Scheme.Modules.unitSection ⊤) (Scheme.Modules.isFrameOn_unitSection ⊤)
    σ cv hσ ⟨⊤, hX⟩ le_rfl
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, hX⟩) (Set.mem_univ p)]
  erw [hid]
  have hmap : X.presheaf.map (homOfLE (le_rfl : (⊤ : X.Opens) ≤ ⊤)).op cv = cv := by
    have : (homOfLE (le_rfl : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, X.presheaf.map_id]; rfl
  rw [hmap]
  show p ∈ X.zeroLocus (↑(Ideal.span {cv}) : Set Γ(X, ⊤)) ↔ _
  rw [Scheme.zeroLocus_span]

end LComb

open AlgebraicGeometry.SmoothProperCurve.LIFT2Aux in
set_option maxHeartbeats 1600000 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N)
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (m : ℕ) (hm : 2 * g ≤ m) (hm₁ : 1 ≤ m) :
    ∃ s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule,
      ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
  classical
  let X : Scheme.{u} := Spec (CommRingCat.of R)
  let M : C.Modules := (ε.1.ker ^ m).invModule
  have hker : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c) ε.1 ε.2
  have hM : Scheme.Modules.IsInvertible M := (hker.pow m).isInvertible_invModule
  have hL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ε.1).obj M) := hM.pullback ε.1
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free R hPic _ hL
  have hX : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X

  have hbo : ∀ (f : Γ(X, ⊤)) (p : X), p ∈ X.basicOpen f ↔ f ∉ (X.toSpecΓ.base p).asIdeal := by
    intro f p
    rw [← PrimeSpectrum.mem_basicOpen, ← Scheme.toSpecΓ_preimage_basicOpen]
    rfl

  have key : ∀ (s : 𝟙_ C.Modules ⟶ M) (p : X),
      ε.1.base p ∈ (Scheme.Modules.zeroSchemeIdeal s).support ↔ LComb.cval ε.1 e s ∈ (X.toSpecΓ.base p).asIdeal := by
    intro s p
    rw [LComb.mem_support_iff ε.1 e hM s p,
      LComb.mem_support_iff_mem_zeroLocus hX _ _ (LComb.app_pullbackSection_comp ε.1 e s) p,
      Scheme.mem_zeroLocus_iff]
    simp only [Set.mem_singleton_iff, forall_eq, hbo, not_not]

  have hεc : ∀ a : Γ(X, ⊤), ε.1.appTop (c.appTop a) = a := by
    intro a
    have h : Scheme.Hom.appTop (ε.1 ≫ c) = Scheme.Hom.appTop (𝟙 X) :=
      congrArg (fun φ : X ⟶ X => Scheme.Hom.appTop φ) ε.2
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
    exact ConcreteCategory.congr_hom h a

  have hI : Ideal.span (Set.range (LComb.cval ε.1 e (M := M))) = ⊤ := by
    by_contra hne
    obtain ⟨m', hm', hle⟩ := Ideal.exists_le_maximal _ hne
    let q : PrimeSpectrum Γ(X, ⊤) := ⟨m', hm'.isPrime⟩
    let 𝔪 : X := (Scheme.homeoOfIso X.isoSpec).symm q
    have hq𝔪 : X.toSpecΓ.base 𝔪 = q := by
      have h1 : (Scheme.homeoOfIso X.isoSpec) 𝔪 = q := (Scheme.homeoOfIso X.isoSpec).apply_symm_apply q
      rw [← h1, ← Scheme.isoSpec_hom]
      rfl
    have h𝔪 : 𝔪.asIdeal.IsMaximal := by
      rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      have hq : IsClosed ({q} : Set (PrimeSpectrum Γ(X, ⊤))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hm'
      have himg : IsClosed (⇑(Scheme.homeoOfIso X.isoSpec).symm '' {q}) :=
        (Scheme.homeoOfIso X.isoSpec).symm.isClosedMap _ hq
      have heq : (⇑(Scheme.homeoOfIso X.isoSpec).symm '' {q} : Set X) = {(Scheme.homeoOfIso X.isoSpec).symm q} :=
        Set.image_singleton
      rw [heq] at himg
      exact himg
    obtain ⟨s, hs⟩ := AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_notMem_support_of_isMaximal R c ε 𝒱 g hg m hm hm₁ 𝔪 h𝔪
    apply hs
    rw [key, hq𝔪]
    exact hle (Ideal.subset_span ⟨s, rfl⟩)

  have h1 : (1 : Γ(X, ⊤)) ∈ Ideal.span (Set.range (LComb.cval ε.1 e (M := M))) := hI ▸ Submodule.mem_top
  obtain ⟨coef, hcoef⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h1

  have hμ : ∀ (s : 𝟙_ C.Modules ⟶ M) (a : Γ(X, ⊤)), ∃ μ : 𝟙_ C.Modules ⟶ M,
      LComb.cval ε.1 e μ = a * LComb.cval ε.1 e s := by
    intro s a
    obtain ⟨μ, hμ⟩ := exists_hom_app_top_eq (N := M) (c.appTop a • s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
    exact ⟨μ, by rw [LComb.cval_smul ε.1 e (c.appTop a) s μ hμ, hεc]⟩
  choose μ hμ' using hμ
  refine ⟨coef.sum fun s a => μ s a, ?_⟩
  have hval : LComb.cval ε.1 e (coef.sum fun s a => μ s a) = 1 := by
    rw [Finsupp.sum, LComb.cval_sum]
    simp only [hμ']
    rw [← hcoef, Finsupp.sum]
    rfl
  rintro x ⟨p, rfl⟩ hx
  rw [key, hval] at hx
  exact (X.toSpecΓ.base p).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hx)

end S_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free (solution)
