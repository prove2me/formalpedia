-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3a9aa33c-ed7c-58da-9e5e-a2f4f5a3a96d

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_range_subset_connectedComponentIn_fibre_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
import Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
import Theorems.Thm_AlgebraicGeometry_RelPicard_support_zeroSchemeIdeal_fibre_subset_of_support_zeroSchemeIdeal_fibre_subset_extension
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry.RelPicard NeronModelInfra"

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

open AlgebraicGeometry.SmoothProperCurve TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage pullbackSpecIso_inv_snd SmoothOfRelativeDimension IsProper Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.preimage_inf isPullback_morphismRestrict Spec Spec.map Scheme Smooth pullbackSpecIso IsOpenImmersion Scheme.Hom.comp_appTop Spec.map_injective Flat pullbackSpecIso_inv_fst IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules.pullbackCongr Spec.map_id Etale Scheme.Hom.preimage_sup Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage IsAffineHom isReduced_of_isOpenImmersion Scheme.Hom.comp_apply geometrically Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd mapOnProdOver_snd_assoc Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom graphOver graphOver_fst graphOver_snd Scheme.Modules.zeroSchemeIdeal prodKerGraph Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections RelPicard.twoGluedSmoothCurveDegenerations_baseChange RelPicard.preimage_range_subset_connectedComponentIn_fibre_baseChange RelPicard.preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension RelPicard.support_zeroSchemeIdeal_fibre_subset_of_support_zeroSchemeIdeal_fibre_subset_extension Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso prodKerGraph_comap_mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.IdealSheafData.comap_mul Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionIdeal fibreModule sectionFibrePoint exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections twoGluedSmoothCurveDegenerations_baseChange preimage_range_subset_connectedComponentIn_fibre_baseChange preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension support_zeroSchemeIdeal_fibre_subset_of_support_zeroSchemeIdeal_fibre_subset_extension exists_fibreIso_hom_comp_eq"
namespace HCoverPrime
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem exists_fibreIso_baseChange {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (baseChange R c A) x' ≅ pullback c (x' ≫ specMap R A),
      φ.hom ≫ pullback.snd c (x' ≫ specMap R A) = pullback.snd (baseChange R c A) x' ∧
      φ.hom ≫ pullback.fst c (x' ≫ specMap R A) = pullback.fst (baseChange R c A) x' ≫ pullback.fst c (specMap R A) := by
  obtain ⟨φ, h1, h2, -⟩ := exists_fibreIso_hom_comp_eq c (specMap R A) x' (x' ≫ specMap R A) rfl
  exact ⟨φ, h1, h2⟩

theorem exists_cutFibreIso_baseChange {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) (x' ≫ specMap R A) ≅
        pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x',
      φ.hom ≫ fibreAt (baseChange R c A) (𝟙 _) x' = fibreAt c (𝟙 _) (x' ≫ specMap R A) := by

  obtain ⟨φ₁, h₁, -, -⟩ := exists_fibreIso_hom_comp_eq c (𝟙 (Spec (CommRingCat.of R))) (x' ≫ specMap R A)
    (x' ≫ specMap R A) (Category.comp_id _)
  obtain ⟨φ₂, h₂, -⟩ := exists_fibreIso_baseChange c A x'
  obtain ⟨φ₃, h₃, -, -⟩ := exists_fibreIso_hom_comp_eq (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) x' x'
    (Category.comp_id _)
  refine ⟨φ₁ ≪≫ φ₂.symm ≪≫ φ₃.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← h₃, Iso.inv_hom_id_assoc, ← h₂, Iso.inv_hom_id_assoc, h₁]

theorem hg_baseChange (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x').TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt (baseChange R c A) (𝟙 _) x')
        (SheafOfModules.unit (pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x').ringCatSheaf)).H1 = g := by
  intro k _ _ x' 𝒲
  obtain ⟨φ, hφ⟩ := exists_cutFibreIso_baseChange c A x'
  obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) (x' ≫ specMap R A)) (fibreAt (baseChange R c A) (𝟙 _) x') φ hφ 𝒲
    (𝟙_ _) (𝟙_ _)
    (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  change Module.finrank k (𝒲.sectionsOf (fibreAt (baseChange R c A) (𝟙 _) x') (𝟙_ _)).H1 = g
  rw [← e1.finrank_eq]
  exact hg k (x' ≫ specMap R A) 𝒱

theorem smooth_U_baseChange (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] :
    SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) := by

  have hsq : IsPullback ((pullback.fst c (specMap R A)) ∣_ U) (pullback.fst c (specMap R A) ⁻¹ᵁ U).ι U.ι
      (pullback.fst c (specMap R A)) := isPullback_morphismRestrict _ _
  have hbig : IsPullback ((pullback.fst c (specMap R A)) ∣_ U)
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) (U.ι ≫ c) (specMap R A) :=
    hsq.paste_vert (IsPullback.of_hasPullback c (specMap R A))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance

theorem hεU_baseChange (U : C.Opens) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hεU : Set.range ε.1 ⊆ (U : Set C)) :
    Set.range (sectionBaseChange A ε).1 ⊆ ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) :
      Set ↥(pullback c (specMap R A))) := by
  rintro _ ⟨z, rfl⟩
  show (pullback.fst c (specMap R A)) ((sectionBaseChange A ε).1 z) ∈ U
  rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
  exact hεU ⟨_, rfl⟩

theorem hH0_baseChange
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤))) :
    ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A'), ⊤)) := by
  intro A' _ _

  letI algRA' : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  have hspec : Scheme.TwoAffineOpenCover.specMap A A' ≫ specMap R A = Scheme.TwoAffineOpenCover.specMap R A' := by
    show Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let ψ : Limits.pullback (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A') ≅
      Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A') :=
    pullbackLeftPullbackSndIso c (specMap R A) (Scheme.TwoAffineOpenCover.specMap A A') ≪≫ pullback.congrHom rfl hspec
  have hψ : ψ.hom ≫ Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A') =
      Limits.pullback.snd (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A') := by
    simp only [ψ, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_snd _ _ _

  letI i1 := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
  letI i2 := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A')) ⊤
  have eTop : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), f.appLE ⊤ ⊤ le_top = f.appTop := fun f =>
    (Scheme.Hom.app_eq_appLE f).symm
  have key : ∀ a : A', i2.algebraMap a = (ψ.hom.appTop).hom (i1.algebraMap a) := by
    intro a
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, eTop, eTop,
      ← hψ, Scheme.Hom.comp_appTop]
    rfl
  haveI : IsIso ψ.hom.appTop := (inferInstance : IsIso (ψ.hom.app ⊤))
  have hiso : Function.Bijective (ψ.hom.appTop).hom := ConcreteCategory.bijective_of_isIso ψ.hom.appTop
  show Function.Bijective i2.algebraMap
  have : (i2.algebraMap : A' → _) = (ψ.hom.appTop).hom ∘ i1.algebraMap := funext key
  rw [this]
  exact hiso.comp (hH0 A')

section blocks

variable (B : Type u) [CommRing B] [Algebra R B] (z : Spec (CommRingCat.of B) ⟶ C)
  (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

theorem includeLeftRingHom_eq_algebraMap :
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) = algebraMap A (A ⊗[R] B) :=
  RingHom.ext fun _ => rfl

noncomputable abbrev incR : Spec (CommRingCat.of (A ⊗[R] B)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom)

include hz in
theorem incR_comm : (incR A B ≫ z) ≫ c =
    Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))) ≫ specMap R A := by
  rw [Category.assoc, hz]
  change _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  rw [← IsScalarTower.algebraMap_eq R A (A ⊗[R] B)]
  exact (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).comp_algebraMap

noncomputable def zA : Spec (CommRingCat.of (A ⊗[R] B)) ⟶ pullback c (specMap R A) :=
  pullback.lift (incR A B ≫ z) (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B)))) (incR_comm c A B z hz)

@[scoped simp] theorem zA_fst : zA c A B z hz ≫ pullback.fst c (specMap R A) = incR A B ≫ z := pullback.lift_fst _ _ _

@[scoped simp] theorem zA_snd : zA c A B z hz ≫ baseChange R c A = Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))) :=
  pullback.lift_snd _ _ _

theorem isPullback_spec_tensor :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B)))) (incR A B) (specMap R A)
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  have h1 := pullbackSpecIso_inv_fst R A B
  have h2 := pullbackSpecIso_inv_snd R A B
  rw [includeLeftRingHom_eq_algebraMap] at h1
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso R A B).symm h1 h2
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  rw [← IsScalarTower.algebraMap_eq R A (A ⊗[R] B)]
  exact ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).comp_algebraMap).symm

theorem isPullback_zA : IsPullback (zA c A B z hz) (incR A B) (pullback.fst c (specMap R A)) z := by
  refine IsPullback.of_right (h₁₂ := baseChange R c A) (v₁₃ := specMap R A) (h₂₂ := c) ?_ (zA_fst c A B z hz)
    (IsPullback.of_hasPullback c (specMap R A)).flip
  rw [zA_snd, hz]
  exact isPullback_spec_tensor A B

scoped instance isClosedImmersion_zA [IsClosedImmersion z] : IsClosedImmersion (zA c A B z hz) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_zA c A B z hz).flip inferInstance

theorem range_zA_subset (U : C.Opens) (hzU : Set.range z.base ⊆ (U : Set C)) :
    Set.range (zA c A B z hz).base ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) := by
  rintro _ ⟨q, rfl⟩
  show (pullback.fst c (specMap R A)) ((zA c A B z hz) q) ∈ U
  rw [← Scheme.Hom.comp_apply, zA_fst, Scheme.Hom.comp_apply]
  exact hzU ⟨_, rfl⟩

theorem fst_mem_range_of_mem_range_zA {p : ↥(pullback c (specMap R A))} (hp : p ∈ Set.range (zA c A B z hz).base) :
    (pullback.fst c (specMap R A)) p ∈ Set.range z.base := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨incR A B q, ?_⟩
  show _ = (pullback.fst c (specMap R A)) ((zA c A B z hz) q)
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, zA_fst]

theorem exists_fac_zA {y0 : Spec (CommRingCat.of A) ⟶ pullback c (specMap R A)}
    (y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)) (hy : y0 ≫ pullback.fst c (specMap R A) = y ≫ z) :
    ∃ y' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (A ⊗[R] B)), y0 = y' ≫ zA c A B z hz :=
  ⟨(isPullback_zA c A B z hz).lift y0 y hy, ((isPullback_zA c A B z hz).lift_fst y0 y hy).symm⟩

end blocks

theorem pairwise_disjoint_range_zA {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) :
    Pairwise fun i j => Disjoint (Set.range (zA c A (B i) (z i) (hz i)).base)
      (Set.range (zA c A (B j) (z j) (hz j)).base) := by
  intro i j hij
  exact Set.disjoint_left.2 fun p hpi hpj =>
    Set.disjoint_left.1 (hzdisj hij) (fst_mem_range_of_mem_range_zA c A (B i) (z i) (hz i) hpi)
      (fst_mem_range_of_mem_range_zA c A (B j) (z j) (hz j) hpj)

theorem range_fst_subset_of_smooth (U : C.Opens)
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    {k : Type u} [Field k] [IsAlgClosed k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
    (hsm : Smooth (pullback.snd (baseChange R c A) x')) :
    Set.range (pullback.fst (baseChange R c A) x').base ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) := by
  obtain ⟨φ, h1, h2⟩ := exists_fibreIso_baseChange c A x'
  have hinv : φ.inv ≫ pullback.snd (baseChange R c A) x' = pullback.snd c (x' ≫ specMap R A) := by
    rw [← h1, Iso.inv_hom_id_assoc]
  haveI : Smooth (pullback.snd c (x' ≫ specMap R A)) := by
    rw [← hinv]
    infer_instance
  have hU := hgoodU k (x' ≫ specMap R A) inferInstance
  rintro _ ⟨p, rfl⟩
  show (pullback.fst c (specMap R A)) ((pullback.fst (baseChange R c A) x') p) ∈ U
  rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
  exact hU ⟨_, rfl⟩

theorem hgred_baseChange
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), IsReduced (pullback (baseChange R c A) x') := by
  intro k _ _ x'
  obtain ⟨φ, -, -⟩ := exists_fibreIso_baseChange c A x'
  haveI := hgred k (x' ≫ specMap R A)
  exact isReduced_of_isOpenImmersion φ.hom

theorem disjoint_range_zA_zA' {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) :
    ∀ i j, Disjoint (Set.range (zA c A (B i) (z i) (hz i)).base) (Set.range (zA c A (B' j) (z' j) (hz' j)).base) := by
  intro i j
  exact Set.disjoint_left.2 fun p hpi hpj =>
    Set.disjoint_left.1 (hzz' i j) (fst_mem_range_of_mem_range_zA c A (B i) (z i) (hz i) hpi)
      (fst_mem_range_of_mem_range_zA c A (B' j) (z' j) (hz' j) hpj)

section split

variable (B : Type u) [CommRing B] [Algebra R B] {d : ℕ} (φ : A ⊗[R] B ≃ₐ[A] (Fin d → A))

include φ in
theorem moduleFinite_of_split : Module.Finite A (A ⊗[R] B) :=
  Module.Finite.equiv φ.symm.toLinearEquiv

include φ in
theorem etale_of_split : Algebra.Etale A (A ⊗[R] B) :=
  Algebra.Etale.of_equiv φ.symm

def splitA : A ⊗[A] (A ⊗[R] B) ≃ₐ[A] (Fin d → A) :=
  (Algebra.TensorProduct.lid A (A ⊗[R] B)).trans φ

end split

section fac

variable (B : Type u) [CommRing B] [Algebra R B] (z : Spec (CommRingCat.of B) ⟶ C)
  (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

theorem exists_algHom_fac_zA (σ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)) (hy : σ₀.1 ≫ pullback.fst c (specMap R A) = y ≫ z)
    (Ω : Type u) [Field Ω] [Algebra A Ω] :
    ∃ ψ : (A ⊗[R] B) →ₐ[A] Ω,
      Scheme.TwoAffineOpenCover.specMap A Ω ≫ σ₀.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ zA c A B z hz := by
  obtain ⟨y', hy'⟩ := exists_fac_zA c A B z hz y hy

  have hsec : y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))) = 𝟙 _ := by
    rw [← zA_snd c A B z hz, ← Category.assoc, ← hy']
    exact σ₀.2

  let χ : (A ⊗[R] B) →+* A := (Spec.preimage y').hom
  have hχ : Spec.map (CommRingCat.ofHom χ) = y' := by
    simp only [χ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hχalg : χ.comp (algebraMap A (A ⊗[R] B)) = RingHom.id A := by
    have h1 : Spec.map (CommRingCat.ofHom (χ.comp (algebraMap A (A ⊗[R] B)))) = Spec.map (CommRingCat.ofHom (RingHom.id A)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hχ, hsec, CommRingCat.ofHom_id, Spec.map_id]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hcomm : ∀ a : A, χ (algebraMap A (A ⊗[R] B) a) = a := fun a => by
    have := congrArg (fun h : A →+* A => h a) hχalg
    simpa using this

  let ψ : (A ⊗[R] B) →ₐ[A] Ω :=
    { toRingHom := (algebraMap A Ω).comp χ
      commutes' := fun a => by
        change algebraMap A Ω (χ (algebraMap A (A ⊗[R] B) a)) = algebraMap A Ω a
        rw [hcomm] }
  refine ⟨ψ, ?_⟩
  change Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ σ₀.1 = Spec.map (CommRingCat.ofHom ((algebraMap A Ω).comp χ)) ≫ _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hχ, ← hy']

end fac

section liftEq

variable (B : Type u) [CommRing B] [Algebra R B] (z : Spec (CommRingCat.of B) ⟶ C)
  (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

theorem lift_zA_eq (zAH : Spec (CommRingCat.of (A ⊗[R] B)) ⟶ pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))))
    (hzA : zAH ≫ pullback.fst (baseChange R c A) (𝟙 _) ≫ pullback.fst c (specMap R A) = incR A B ≫ z)
    (hzA' : zAH ≫ pullback.snd (baseChange R c A) (𝟙 _) = Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B)))) :
    pullback.lift (zA c A B z hz) (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))))
      (by rw [Category.comp_id]; exact zA_snd c A B z hz) = zAH := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    apply pullback.hom_ext
    · rw [zA_fst, Category.assoc, hzA]
    · rw [zA_snd, Category.assoc]
      have := pullback.condition (f := baseChange R c A) (g := 𝟙 (Spec (CommRingCat.of A)))
      rw [Category.comp_id] at this
      rw [this, hzA']
  · rw [pullback.lift_snd, hzA']

end liftEq

theorem isAlgEquivZero_geom
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] (sg : Spec (CommRingCat.of Ω) ⟶ T) (hsg : sg ≫ t = specMap R Ω) :
    IsAlgEquivZero (pullback.snd c (specMap R Ω)) ((Scheme.Modules.pullback (mapOnProdOver c sg hsg)).obj L.L) := by
  obtain ⟨φ, h1, -, h3⟩ := exists_fibreIso_hom_comp_eq c t sg (specMap R Ω) hsg
  have h0 : IsAlgEquivZero (fibreAt c t sg) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) sg)).obj L.L) := hL Ω sg
  have h1' : φ.inv ≫ fibreAt c t sg = pullback.snd c (specMap R Ω) := by
    rw [← h1, Iso.inv_hom_id_assoc]
  have h3' : φ.inv ≫ pullback.fst (pullback.snd c t) sg = mapOnProdOver c sg hsg := by
    rw [← h3, Iso.inv_hom_id_assoc]
    rfl
  have h := h0.pullback φ.inv (a' := pullback.snd c (specMap R Ω)) h1'
  refine h.of_iso ?_
  exact (Scheme.Modules.pullbackComp _ _).app L.L ≪≫ (Scheme.Modules.pullbackCongr h3').app L.L

namespace Beta

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

def comapCover {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i] (𝒲 : X.TwoAffineOpenCover) :
    Y.TwoAffineOpenCover where
  U0 := i ⁻¹ᵁ 𝒲.U0
  U1 := i ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage _
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage _
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage _

theorem mapOnProdOver_comp {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T T' T'' : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of R)} {g' : T' ⟶ Spec (CommRingCat.of R)}
    {g'' : T'' ⟶ Spec (CommRingCat.of R)} (φ : T ⟶ T') (hφ : φ ≫ g' = g) (ψ : T' ⟶ T'') (hψ : ψ ≫ g'' = g') :
    mapOnProdOver c φ hφ ≫ mapOnProdOver c ψ hψ = mapOnProdOver c (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mapOnProdOver_fst]
  · simp only [Category.assoc, mapOnProdOver_snd, mapOnProdOver_snd_assoc]

end Beta

open Beta in
theorem beta
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {ρ e e₁ e₂ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    (p : Fin e₁ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (p' : Fin e₂ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDU : D.SupportedIn U)
    (hDI : D.I = prodKerGraph c (fun j => (p j).1) (fun j => (p j).2) * prodKerGraph c (fun j => (p' j).1) (fun j => (p' j).2))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (Ω : Type u) [Field Ω] [Algebra R Ω] (sg : Spec (CommRingCat.of Ω) ⟶ T) (hsg : sg ≫ t = specMap R Ω)
    (hgeom :
      (∀ 𝒲 : (pullback c (specMap R Ω)).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (pullback.snd c (specMap R Ω))
          ((Scheme.Modules.pullback (mapOnProdOver c sg hsg)).obj L.L ⊗
            ((E.pullbackAlong (specMap R Ω) (Category.comp_id _)).lineBundle ⊗
              ((∏ j, (graphOver c (specMap R Ω ≫ (p j).1) (by rw [Category.assoc, (p j).2, Category.comp_id])).ker) *
               (∏ j, (graphOver c (specMap R Ω ≫ (p' j).1) (by rw [Category.assoc, (p' j).2, Category.comp_id])).ker)).module))).H1) ∧
      (∀ τ : 𝟙_ (pullback c (specMap R Ω)).Modules ⟶
          ((Scheme.Modules.pullback (mapOnProdOver c sg hsg)).obj L.L ⊗
            ((E.pullbackAlong (specMap R Ω) (Category.comp_id _)).lineBundle ⊗
              ((∏ j, (graphOver c (specMap R Ω ≫ (p j).1) (by rw [Category.assoc, (p j).2, Category.comp_id])).ker) *
               (∏ j, (graphOver c (specMap R Ω ≫ (p' j).1) (by rw [Category.assoc, (p' j).2, Category.comp_id])).ker)).module)),
        τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (specMap R Ω))) ⊆
          ((pullback.fst c (specMap R Ω)) ⁻¹ᵁ U : Set ↥(pullback c (specMap R Ω))))) :
    (∀ 𝒲 : (pullback (pullback.snd c t) sg).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t sg) (fibreModule c t sg
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (D.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) ∧
    (∀ τ : 𝟙_ (pullback c (sg ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c sg rfl)).obj
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (D.pullbackAlong t (Category.comp_id t)).idealModule)),
      τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (sg ≫ t))) ⊆
        ((pullback.fst c (sg ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (sg ≫ t)))) := by
  classical

  revert hgeom
  revert hsg
  generalize specMap R Ω = x
  intro hsg hgeom
  subst hsg
  obtain ⟨hgeom1, hgeom2⟩ := hgeom

  set ψ : pullback c (sg ≫ t) ⟶ pullback c t := mapOnProdOver c sg rfl with hψ
  have hψt : ψ ≫ mapOnProdOver c t (Category.comp_id t) = mapOnProdOver c (sg ≫ t) (Category.comp_id _) := by
    rw [hψ, mapOnProdOver_comp]

  have hEt : (E.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t (Category.comp_id t))
  have hEs : (E.pullbackAlong (sg ≫ t) (Category.comp_id _)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong (sg ≫ t) (Category.comp_id _))
  have hDt : (D.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hDU.pullbackAlong t (Category.comp_id t))
  have hDs : (D.pullbackAlong (sg ≫ t) (Category.comp_id _)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hDU.pullbackAlong (sg ≫ t) (Category.comp_id _))

  have hEcomap : (E.pullbackAlong t (Category.comp_id t)).I.comap ψ = (E.pullbackAlong (sg ≫ t) (Category.comp_id _)).I := by
    show (E.I.comap (mapOnProdOver c t (Category.comp_id t))).comap ψ = E.I.comap (mapOnProdOver c (sg ≫ t) (Category.comp_id _))
    rw [← Scheme.IdealSheafData.comap_comp, hψt]
  have hDcomap : (D.pullbackAlong t (Category.comp_id t)).I.comap ψ = (D.pullbackAlong (sg ≫ t) (Category.comp_id _)).I := by
    show (D.I.comap (mapOnProdOver c t (Category.comp_id t))).comap ψ = D.I.comap (mapOnProdOver c (sg ≫ t) (Category.comp_id _))
    rw [← Scheme.IdealSheafData.comap_comp, hψt]

  have hDgraph : (D.pullbackAlong (sg ≫ t) (Category.comp_id _)).I =
      (∏ j, (graphOver c ((sg ≫ t) ≫ (p j).1) (by rw [Category.assoc, (p j).2, Category.comp_id])).ker) *
        (∏ j, (graphOver c ((sg ≫ t) ≫ (p' j).1) (by rw [Category.assoc, (p' j).2, Category.comp_id])).ker) := by
    show D.I.comap (mapOnProdOver c (sg ≫ t) (Category.comp_id _)) = _
    rw [hDI, Scheme.IdealSheafData.comap_mul, prodKerGraph_comap_mapOnProdOver, prodKerGraph_comap_mapOnProdOver]
    rfl

  obtain ⟨eE⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso ψ hEt (by rw [hEcomap]; exact hEs)
  haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison ψ hDt (by rw [hDcomap]; exact hDs)
  let eD : (Scheme.Modules.pullback ψ).obj (D.pullbackAlong t (Category.comp_id t)).idealModule ≅
      ((∏ j, (graphOver c ((sg ≫ t) ≫ (p j).1) (by rw [Category.assoc, (p j).2, Category.comp_id])).ker) *
        (∏ j, (graphOver c ((sg ≫ t) ≫ (p' j).1) (by rw [Category.assoc, (p' j).2, Category.comp_id])).ker)).module :=
    asIso ((D.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison ψ) ≪≫ eqToIso (by rw [hDcomap, hDgraph])
  let eE' : (Scheme.Modules.pullback ψ).obj (E.pullbackAlong t (Category.comp_id t)).lineBundle ≅
      (E.pullbackAlong (sg ≫ t) (Category.comp_id _)).lineBundle :=
    eE ≪≫ eqToIso (by rw [hEcomap])
  let eψ : (Scheme.Modules.pullback ψ).obj
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (D.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
      (Scheme.Modules.pullback ψ).obj L.L ⊗
        ((E.pullbackAlong (sg ≫ t) (Category.comp_id _)).lineBundle ⊗
          ((∏ j, (graphOver c ((sg ≫ t) ≫ (p j).1) (by rw [Category.assoc, (p j).2, Category.comp_id])).ker) *
           (∏ j, (graphOver c ((sg ≫ t) ≫ (p' j).1) (by rw [Category.assoc, (p' j).2, Category.comp_id])).ker)).module) :=
    Scheme.Modules.pullbackTensorObjIso ψ _ _ ≪≫
      whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso ψ _ _ ≪≫ (eE' ⊗ᵢ eD))

  refine ⟨fun 𝒲 => ?_, fun τ hτ => ?_⟩
  ·
    obtain ⟨φ, hφsnd, -, hφbcs⟩ := exists_fibreIso_hom_comp_eq c t sg (sg ≫ t) rfl
    have hbcs : baseChangeSnd c (⟨sg, rfl⟩ : SchemeHomOver (sg ≫ t) t) = ψ := by
      apply pullback.hom_ext
      · rw [hψ, mapOnProdOver_fst]; unfold baseChangeSnd; rw [pullback.lift_fst, Category.comp_id]
      · rw [hψ, mapOnProdOver_snd]; unfold baseChangeSnd; rw [pullback.lift_snd]
    have hfst : pullback.fst (pullback.snd c t) sg = φ.hom ≫ ψ := by rw [← hφbcs, hbcs]

    let e₁ : fibreModule c t sg
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (D.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
        (Scheme.Modules.pullback φ.hom).obj
          ((Scheme.Modules.pullback ψ).obj L.L ⊗
            ((E.pullbackAlong (sg ≫ t) (Category.comp_id _)).lineBundle ⊗
              ((∏ j, (graphOver c ((sg ≫ t) ≫ (p j).1) (by rw [Category.assoc, (p j).2, Category.comp_id])).ker) *
               (∏ j, (graphOver c ((sg ≫ t) ≫ (p' j).1) (by rw [Category.assoc, (p' j).2, Category.comp_id])).ker)).module)) :=
      (Scheme.Modules.pullbackCongr hfst).app _ ≪≫ ((Scheme.Modules.pullbackComp φ.hom ψ).app _).symm ≪≫
        (Scheme.Modules.pullback φ.hom).mapIso eψ

    haveI : IsAffineHom φ.inv := inferInstance
    let 𝒱' : (pullback c (sg ≫ t)).TwoAffineOpenCover := comapCover φ.inv 𝒲
    obtain ⟨𝒱₂, h0, h1, -, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c t sg) (pullback.snd c (sg ≫ t)) φ hφsnd 𝒱' _ _ e₁
    have h𝒱 : 𝒱₂ = 𝒲 := by
      apply cover_ext
      · rw [h0]; show φ.hom ⁻¹ᵁ (φ.inv ⁻¹ᵁ 𝒲.U0) = 𝒲.U0
        rw [← Scheme.Hom.comp_preimage, Iso.hom_inv_id]; rfl
      · rw [h1]; show φ.hom ⁻¹ᵁ (φ.inv ⁻¹ᵁ 𝒲.U1) = 𝒲.U1
        rw [← Scheme.Hom.comp_preimage, Iso.hom_inv_id]; rfl
    subst h𝒱
    haveI := hgeom1 𝒱'
    exact f1.toEquiv.subsingleton
  · have hτ' : τ ≫ eψ.hom ≠ 0 := fun h => hτ (by
      have h' := congrArg (· ≫ eψ.inv) h
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Limits.zero_comp] at h'
      exact h')
    have := hgeom2 (τ ≫ eψ.hom) hτ'
    rwa [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso] at this

end AlgebraicGeometry.RelPicard.HCoverPrime
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry.RelPicard.HCoverPrime"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective.AlgebraicGeometry"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεA : Set.range ε.1 ⊆ (U : Set C))
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A]

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i) (φ' : ∀ i, TensorProduct R A (B' i) ≃ₐ[A] (Fin (deg' i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) [∀ i, IsClosedImmersion (z' i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M'),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range (z' i).base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (σ' : ∀ i, Fin (deg' i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (hσfac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
    (hσ'fac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B' i)),
      (σ' i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z' i)
    (hσinj : ∀ i, Function.Injective (σ i)) (hσ'inj : ∀ i, Function.Injective (σ' i))

    (r r' : ℕ) (i₀ : Fin M') (e ρ : ℕ) (hρ : ρ = r + r' * deg' i₀) (he : g + e = ρ)
    (hr : 2 * g + 1 ≤ r) (hr' : 2 * g + 1 ≤ r')

    (zA : Spec (CommRingCat.of (TensorProduct R A (B' i₀))) ⟶ pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))))
    [IsClosedImmersion zA]
    (hzA : zA ≫ pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) ≫ pullback.fst c (specMap R A) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B' i₀)).toRingHom) ≫ z' i₀)
    (hzA' : zA ≫ pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A (B' i₀)))))

    (E : RelEffCartierDiv (baseChange R c A) ρ (𝟙 (Spec (CommRingCat.of A))))
    (hEI : E.I = (sectionIdeal (baseChange R c A) (sectionBaseChange A ε) (𝟙 (Spec (CommRingCat.of A)))) ^ r * zA.ker ^ r')
    (hEU : E.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))

    {ι : Type u}
    (idx : ∀ (e₁ e₂ : ℕ), e₁ + e₂ = e → {a : Fin e₁ → Fin M // Function.Injective a} →
      {a' : Fin e₂ → Fin M' // Function.Injective a'} → (∀ i, Fin (deg i)) → (∀ i, Fin (deg' i)) → ι)
    (Dγ : ι → RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDγI : ∀ (e₁ e₂ : ℕ) (he₁₂ : e₁ + e₂ = e) (a : {a : Fin e₁ → Fin M // Function.Injective a})
      (a' : {a' : Fin e₂ → Fin M' // Function.Injective a'}) (m : ∀ i, Fin (deg i)) (m' : ∀ i, Fin (deg' i)),
      (Dγ (idx e₁ e₂ he₁₂ a a' m m')).I =
        prodKerGraph (baseChange R c A) (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2) *
        prodKerGraph (baseChange R c A) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).1) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).2))
    (hDγU : ∀ i, (Dγ i).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)
    (hMlt : (g + 2) * (r + r' * b) * b ^ e + e < M) (hM'lt : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M') :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)) (L : RigidifiedLineBundle (baseChange R c A) (sectionBaseChange A ε) t),
      FibrewiseAlgEquivZero L → ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ i : ι,
        (∀ (𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
            (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1) ∧
        (∀ τ : 𝟙_ (pullback (baseChange R c A) (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver (baseChange R c A) s rfl)).obj
            (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)),
          τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback (baseChange R c A) (s ≫ t))) ⊆
            ((pullback.fst (baseChange R c A) (s ≫ t)) ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
              Set ↥(pullback (baseChange R c A) (s ≫ t)))) := by
  classical
  intro T t L hL k _ s

  haveI := HCoverPrime.smooth_U_baseChange c A U
  haveI : ∀ i, Module.Finite A (A ⊗[R] B i) := fun i => HCoverPrime.moduleFinite_of_split A (B i) (φ i)
  haveI : ∀ i, Algebra.Etale A (A ⊗[R] B i) := fun i => HCoverPrime.etale_of_split A (B i) (φ i)
  haveI : ∀ i, Module.Finite A (A ⊗[R] B' i) := fun i => HCoverPrime.moduleFinite_of_split A (B' i) (φ' i)
  haveI : ∀ i, Algebra.Etale A (A ⊗[R] B' i) := fun i => HCoverPrime.etale_of_split A (B' i) (φ' i)

  let Ω : Type u := AlgebraicClosure k
  let sg : Spec (CommRingCat.of Ω) ⟶ T := Scheme.TwoAffineOpenCover.specMap k Ω ≫ s
  letI algAΩ : Algebra A Ω := (Spec.preimage (sg ≫ t)).hom.toAlgebra
  have hsg : sg ≫ t = specMap A Ω := by
    show sg ≫ t = Spec.map (CommRingCat.ofHom (algebraMap A Ω))
    conv_lhs => rw [← Spec.map_preimage (sg ≫ t)]
    rfl

  have hrange : ∀ {Bx : Type u} [CommRing Bx] [Algebra R Bx] (zx : Spec (CommRingCat.of Bx) ⟶ C)
      (hzx : zx ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Bx))),
      Set.range (HCoverPrime.zA c A Bx zx hzx ≫ pullback.fst c (specMap R A)).base ⊆ Set.range zx.base := by
    intro Bx _ _ zx hzx
    rw [HCoverPrime.zA_fst]
    rintro _ ⟨q, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ q).symm⟩
  have hN11 := AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
    (baseChange R c A) (𝒱.pullback c A) (HCoverPrime.hH0_baseChange c A hH0) (sectionBaseChange A ε)
    (pullback.fst c (specMap R A) ⁻¹ᵁ U) (HCoverPrime.hεU_baseChange c A U ε hεA)
    (fun k _ _ x hsm => HCoverPrime.range_fst_subset_of_smooth c A U hgoodU x hsm)
    (HCoverPrime.hgred_baseChange c A hgred) g (HCoverPrime.hg_baseChange c A g hg)
    (AlgebraicGeometry.RelPicard.twoGluedSmoothCurveDegenerations_baseChange c A ε U hbad)
    A (fun i => A ⊗[R] B i) deg hdeg (fun i => HCoverPrime.splitA A (B i) (φ i))
    (fun i => HCoverPrime.zA c A (B i) (z i) (hz i)) (fun i => HCoverPrime.zA_snd c A (B i) (z i) (hz i))
    (fun i => HCoverPrime.range_zA_subset c A (B i) (z i) (hz i) U (hzU i))
    (HCoverPrime.pairwise_disjoint_range_zA c A B z hz hzdisj)
    (fun k _ _ s' i => AlgebraicGeometry.RelPicard.preimage_range_subset_connectedComponentIn_fibre_baseChange c A ε U
      (z i) (HCoverPrime.zA c A (B i) (z i) (hz i)) (hrange (z i) (hz i)) (fun k _ _ s => hzε k s i) k s')
    (fun i => A ⊗[R] B' i) deg' hdeg' (fun i => HCoverPrime.splitA A (B' i) (φ' i))
    (fun i => HCoverPrime.zA c A (B' i) (z' i) (hz' i)) (fun i => HCoverPrime.zA_snd c A (B' i) (z' i) (hz' i))
    (fun i => HCoverPrime.range_zA_subset c A (B' i) (z' i) (hz' i) U (hz'U i))
    (HCoverPrime.pairwise_disjoint_range_zA c A B' z' hz' hz'disj)
    (HCoverPrime.disjoint_range_zA_zA' c A B B' z hz z' hz' hzz')
    (fun k _ _ s' i hns => AlgebraicGeometry.RelPicard.preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
      c A ε U (z' i) (HCoverPrime.zA c A (B' i) (z' i) (hz' i)) (hrange (z' i) (hz' i)) (fun k _ _ s => hz'ε k s i) k s' hns)
    r r' i₀ e (he.trans hρ) hr hr' b hdegb hdeg'b hMlt hM'lt ρ hρ E
    (by rw [HCoverPrime.lift_zA_eq c A (B' i₀) (z' i₀) (hz' i₀) zA hzA hzA']; exact hEI)
    Ω ((Scheme.Modules.pullback (mapOnProdOver (baseChange R c A) sg hsg)).obj L.L) (L.isInvertible.pullback _)
    (HCoverPrime.isAlgEquivZero_geom (baseChange R c A) (sectionBaseChange A ε) t L hL Ω sg hsg)
  obtain ⟨e₁, e₂, he₁₂, a, a', ha, ha', hgen⟩ := hN11

  let m₀ : ∀ i, Fin (deg i) := fun i => ⟨0, hdeg i⟩
  let m₀' : ∀ i, Fin (deg' i) := fun i => ⟨0, hdeg' i⟩
  refine ⟨idx e₁ e₂ he₁₂ ⟨a, ha⟩ ⟨a', ha'⟩ m₀ m₀', ?_⟩

  have hv : ∀ j, ∃ ψ : (A ⊗[R] B (a j)) →ₐ[A] Ω,
      (graphOver (baseChange R c A) (specMap A Ω ≫ (σ (a j) (m₀ (a j))).1)
        (by rw [Category.assoc, (σ (a j) (m₀ (a j))).2, Category.comp_id])) ≫ pullback.fst (baseChange R c A) (specMap A Ω) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ HCoverPrime.zA c A (B (a j)) (z (a j)) (hz (a j)) := by
    intro j
    obtain ⟨y, hy⟩ := hσfac (a j) (m₀ (a j))
    obtain ⟨ψ, hψ⟩ := HCoverPrime.exists_algHom_fac_zA c A (B (a j)) (z (a j)) (hz (a j)) (σ (a j) (m₀ (a j))) y hy Ω
    exact ⟨ψ, by rw [graphOver_fst]; exact hψ⟩
  have hv' : ∀ j, ∃ ψ : (A ⊗[R] B' (a' j)) →ₐ[A] Ω,
      (graphOver (baseChange R c A) (specMap A Ω ≫ (σ' (a' j) (m₀' (a' j))).1)
        (by rw [Category.assoc, (σ' (a' j) (m₀' (a' j))).2, Category.comp_id])) ≫ pullback.fst (baseChange R c A) (specMap A Ω) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ HCoverPrime.zA c A (B' (a' j)) (z' (a' j)) (hz' (a' j)) := by
    intro j
    obtain ⟨y, hy⟩ := hσ'fac (a' j) (m₀' (a' j))
    obtain ⟨ψ, hψ⟩ := HCoverPrime.exists_algHom_fac_zA c A (B' (a' j)) (z' (a' j)) (hz' (a' j)) (σ' (a' j) (m₀' (a' j))) y hy Ω
    exact ⟨ψ, by rw [graphOver_fst]; exact hψ⟩
  have hgeom := hgen
    (fun j => ⟨graphOver (baseChange R c A) (specMap A Ω ≫ (σ (a j) (m₀ (a j))).1)
      (by rw [Category.assoc, (σ (a j) (m₀ (a j))).2, Category.comp_id]), graphOver_snd _ _ _⟩)
    (fun j => ⟨graphOver (baseChange R c A) (specMap A Ω ≫ (σ' (a' j) (m₀' (a' j))).1)
      (by rw [Category.assoc, (σ' (a' j) (m₀' (a' j))).2, Category.comp_id]), graphOver_snd _ _ _⟩)
    hv hv'

  have hβ := HCoverPrime.beta (baseChange R c A) (pullback.fst c (specMap R A) ⁻¹ᵁ U) (sectionBaseChange A ε) E hEU
    (fun j => σ (a j) (m₀ (a j))) (fun j => σ' (a' j) (m₀' (a' j)))
    (Dγ (idx e₁ e₂ he₁₂ ⟨a, ha⟩ ⟨a', ha'⟩ m₀ m₀')) (hDγU _) (hDγI e₁ e₂ he₁₂ ⟨a, ha⟩ ⟨a', ha'⟩ m₀ m₀')
    t L Ω sg hsg hgeom

  have hM : Scheme.Modules.IsInvertible
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗
        ((Dγ (idx e₁ e₂ he₁₂ ⟨a, ha⟩ ⟨a', ha'⟩ m₀ m₀')).pullbackAlong t (Category.comp_id t)).idealModule)) :=
    L.isInvertible.tensor
      (((AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn _ (E.pullbackAlong t (Category.comp_id t))
          (hEU.pullbackAlong t (Category.comp_id t))).isInvertible_invModule).tensor
        ((AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn _
          ((Dγ (idx e₁ e₂ he₁₂ ⟨a, ha⟩ ⟨a', ha'⟩ m₀ m₀')).pullbackAlong t (Category.comp_id t))
          ((hDγU _).pullbackAlong t (Category.comp_id t))).isInvertible_module))
  refine ⟨?_, ?_⟩
  · exact AlgebraicGeometry.RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension (baseChange R c A) t _ hM s Ω hβ.1
  · exact AlgebraicGeometry.RelPicard.support_zeroSchemeIdeal_fibre_subset_of_support_zeroSchemeIdeal_fibre_subset_extension
      (baseChange R c A) (pullback.fst c (specMap R A) ⁻¹ᵁ U) t _ hM s Ω hβ.2

end S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective (solution)
