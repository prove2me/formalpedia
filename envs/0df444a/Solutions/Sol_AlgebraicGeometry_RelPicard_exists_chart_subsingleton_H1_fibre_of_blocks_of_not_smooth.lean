-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9e073484-0859-5d1b-9b55-0b21446be877

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_twoAffineOpenCover_presentation_comp_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_eq_finrank_H1_add_one_of_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II"
p2m_attr_erase "instance" "DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth.AlgebraicGeometry.RelPicard NeronModelInfra"

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.Hom.preimage_inf Scheme.homeoOfIso Spec Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Smooth pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.Hom.comp_base Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced IsSeparated Scheme.Hom.preimage_sup Scheme.Modules pullbackRestrictIsoRestrict Scheme.Hom.comp_preimage IsAffineHom isReduced_of_isOpenImmersion Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver mapOnProdOver_fst Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom prodKerGraph TwoGluedProjectiveLines.exists_twoAffineOpenCover_presentation_comp_iso TwoGluedProjectiveLines.eq_finrank_H1_add_one_of_finrank_H0_eq_one Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.Modules.pullbackTensorUnitObjIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks isInvertible_sectionIdeal_of_range_subset"
namespace HCoverBad
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem smoothOfRelativeDimension_one_preimage_comp_baseChange {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (A : Type u) [CommRing A] [Algebra R A] :
    SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) := by
  let e : ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Scheme.{u}) ≅
      pullback (U.ι ≫ c) (specMap R A) :=
    (pullbackRestrictIsoRestrict (pullback.fst c (specMap R A)) U).symm ≪≫
      pullbackSymmetry (pullback.fst c (specMap R A)) U.ι ≪≫ pullbackRightPullbackFstIso c (specMap R A) U.ι
  have he : (pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A =
      e.hom ≫ pullback.snd (U.ι ≫ c) (specMap R A) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc]
  rw [he]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.hom ≫ pullback.snd (U.ι ≫ c) (specMap R A)))

theorem range_sectionBaseChange_subset_preimage {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    (hεA : Set.range ε.1 ⊆ (U : Set C)) (A : Type u) [CommRing A] [Algebra R A] :
    Set.range (sectionBaseChange A ε).1 ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) := by
  rintro _ ⟨z, rfl⟩
  change (pullback.fst c (specMap R A)).base ((sectionBaseChange A ε).1.base z) ∈ (U : Set C)
  rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
  exact hεA ⟨_, rfl⟩

end AlgebraicGeometry.RelPicard.HCoverBad

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.Hom.preimage_inf Scheme.homeoOfIso Spec Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Smooth pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.Hom.comp_base Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced IsSeparated Scheme.Hom.preimage_sup Scheme.Modules pullbackRestrictIsoRestrict Scheme.Hom.comp_preimage IsAffineHom isReduced_of_isOpenImmersion Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver mapOnProdOver_fst Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom prodKerGraph TwoGluedProjectiveLines.exists_twoAffineOpenCover_presentation_comp_iso TwoGluedProjectiveLines.eq_finrank_H1_add_one_of_finrank_H0_eq_one Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.Modules.pullbackTensorUnitObjIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks isInvertible_sectionIdeal_of_range_subset"
namespace HCoverBad
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem eq_of_fst_mem_range_rigSection {R : Type u} [CommRing R] {C T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
    (e : Spec (CommRingCat.of K) ⟶ pullback (pullback.snd c t) s)
    (he : e ≫ pullback.fst (pullback.snd c t) s = s ≫ rigSection c t ε)
    (y : ↥(pullback (pullback.snd c t) s))
    (hy : (pullback.fst (pullback.snd c t) s).base y ∈ Set.range (rigSection c t ε).base) :
    y = e.base (IsLocalRing.closedPoint K) := by
  let P' := pullback (rigSection c t ε) (pullback.fst (pullback.snd c t) s)
  have hsub : Subsingleton ↥P' := by
    let eP : P' ≅ pullback (rigSection c t ε ≫ pullback.snd c t) s := pullbackRightPullbackFstIso _ _ _
    haveI : IsIso (rigSection c t ε ≫ pullback.snd c t) := by
      rw [rigSection, pullback.lift_snd]; infer_instance
    haveI : IsIso (pullback.snd (rigSection c t ε ≫ pullback.snd c t) s) := inferInstance
    have hinj : Function.Injective ⇑(eP.hom ≫ pullback.snd (rigSection c t ε ≫ pullback.snd c t) s) :=
      (ConcreteCategory.bijective_of_isIso _).1
    exact ⟨fun p q => hinj (Subsingleton.elim _ _)⟩
  have hrange : Set.range ⇑(pullback.snd (rigSection c t ε) (pullback.fst (pullback.snd c t) s)) =
      ⇑(pullback.fst (pullback.snd c t) s) ⁻¹' Set.range ⇑(rigSection c t ε) := Scheme.Pullback.range_snd _ _
  have hz : y ∈ Set.range ⇑(pullback.snd (rigSection c t ε) (pullback.fst (pullback.snd c t) s)) := by
    rw [hrange]; exact hy
  have hzε : e.base (IsLocalRing.closedPoint K) ∈
      Set.range ⇑(pullback.snd (rigSection c t ε) (pullback.fst (pullback.snd c t) s)) := by
    rw [hrange, Set.mem_preimage, ← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨p₁, hp₁⟩ := hzε
  obtain ⟨p₂, hp₂⟩ := hz
  rw [← hp₂, ← hp₁, Subsingleton.elim p₁ p₂]

section L4

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (A : Type u) [CommRing A] [Algebra R A]
  {K : Type u} [Field K] (s₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)) (U : C.Opens)

theorem sectionFibrePoint_sectionBaseChange_comp_pullbackLeftPullbackSndIso_hom :
    (sectionFibrePoint (sectionBaseChange A ε) s₂).1 ≫ (pullbackLeftPullbackSndIso c (specMap R A) s₂).hom =
      (sectionFibrePoint ε (s₂ ≫ specMap R A)).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
    simp only [sectionFibrePoint, pullback.lift_fst_assoc, Category.assoc, sectionBaseChange_coe_fst, pullback.lift_fst]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
    simp only [sectionFibrePoint, pullback.lift_snd]

omit [Field K] in

theorem pullbackLeftPullbackSndIso_hom_preimage_preimage {K : Type u} [CommRing K]
    (s₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)) :
    (pullbackLeftPullbackSndIso c (specMap R A) s₂).hom ⁻¹ᵁ (pullback.fst c (s₂ ≫ specMap R A) ⁻¹ᵁ U) =
      pullback.fst (baseChange R c A) s₂ ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullbackLeftPullbackSndIso_hom_fst]

theorem image_connectedComponentIn_sectionFibrePoint :
    (pullbackLeftPullbackSndIso c (specMap R A) s₂).hom.base ''
        connectedComponentIn ((pullback.fst (baseChange R c A) s₂ ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
            (pullback (baseChange R c A) s₂).Opens) : Set ↥(pullback (baseChange R c A) s₂))
          (((sectionFibrePoint (sectionBaseChange A ε) s₂).1).base (IsLocalRing.closedPoint K)) =
      connectedComponentIn ((pullback.fst c (s₂ ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s₂ ≫ specMap R A)).Opens) :
          Set ↥(pullback c (s₂ ≫ specMap R A)))
        (((sectionFibrePoint ε (s₂ ≫ specMap R A)).1).base (IsLocalRing.closedPoint K)) := by
  let ψ := pullbackLeftPullbackSndIso c (specMap R A) s₂

  have hψ : ∀ z, Scheme.homeoOfIso ψ z = ψ.hom.base z := fun z => rfl
  have hS : (Scheme.homeoOfIso ψ) '' ((pullback.fst (baseChange R c A) s₂ ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
        (pullback (baseChange R c A) s₂).Opens) : Set ↥(pullback (baseChange R c A) s₂)) =
      ((pullback.fst c (s₂ ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s₂ ≫ specMap R A)).Opens) :
        Set ↥(pullback c (s₂ ≫ specMap R A))) := by
    rw [← pullbackLeftPullbackSndIso_hom_preimage_preimage c A U s₂]
    exact (Scheme.homeoOfIso ψ).image_preimage
      (((pullback.fst c (s₂ ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s₂ ≫ specMap R A)).Opens) :
        Set ↥(pullback c (s₂ ≫ specMap R A))))
  have hx : (Scheme.homeoOfIso ψ) (((sectionFibrePoint (sectionBaseChange A ε) s₂).1).base (IsLocalRing.closedPoint K)) =
      ((sectionFibrePoint ε (s₂ ≫ specMap R A)).1).base (IsLocalRing.closedPoint K) := by
    rw [hψ, ← Scheme.Hom.comp_apply, sectionFibrePoint_sectionBaseChange_comp_pullbackLeftPullbackSndIso_hom]
  change (Scheme.homeoOfIso ψ) '' _ = _
  by_cases hmem : ((sectionFibrePoint (sectionBaseChange A ε) s₂).1).base (IsLocalRing.closedPoint K) ∈
      ((pullback.fst (baseChange R c A) s₂ ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
        (pullback (baseChange R c A) s₂).Opens) : Set ↥(pullback (baseChange R c A) s₂))
  · rw [(Scheme.homeoOfIso ψ).image_connectedComponentIn hmem, hS, hx]
  · rw [connectedComponentIn_eq_empty hmem, Set.image_empty, eq_comm, connectedComponentIn_eq_empty]
    rw [← hx, ← hS]
    exact fun h => hmem ((Scheme.homeoOfIso ψ).injective.mem_set_image.mp h)

end L4

end AlgebraicGeometry.RelPicard.HCoverBad

open AlgebraicGeometry.RelPicard.HCoverBad in
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
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)))
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] (e r : ℕ) (hr : g + e = r)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (hσfac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
    (Dγ : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))) →
      RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDγI : ∀ am, (Dγ am).I = prodKerGraph (baseChange R c A)
      (fun j => (σ (am.down.1.1 j) (am.down.2 (am.down.1.1 j))).1)
      (fun j => (σ (am.down.1.1 j) (am.down.2 (am.down.1.1 j))).2))
    (hDγU : ∀ am, (Dγ am).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))
    (hσinj : ∀ i, Function.Injective (σ i))
    (hgr : 2 * g ≤ r + 1)
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ e + e < M)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A))
    (L : RigidifiedLineBundle (baseChange R c A) (sectionBaseChange A ε) t) (hL : FibrewiseAlgEquivZero L)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ T)
    (hns : ¬ Smooth (pullback.snd (baseChange R c A) (s ≫ t))) :
    ∃ i : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))),
      ∀ 𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
          (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗
            ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by
  classical

  set s₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) := s ≫ t with hs₂
  set sb : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := s₂ ≫ specMap R A with hsb

  obtain ⟨ψ, hψsnd, hψfst, hψε, hψcomp⟩ : ∃ ψ : pullback (baseChange R c A) s₂ ≅ pullback c sb,
      ψ.hom ≫ pullback.snd c sb = pullback.snd (baseChange R c A) s₂ ∧
      ψ.hom ≫ pullback.fst c sb = pullback.fst (baseChange R c A) s₂ ≫ pullback.fst c (specMap R A) ∧
      (sectionFibrePoint (sectionBaseChange A ε) s₂).1 ≫ ψ.hom = (sectionFibrePoint ε sb).1 ∧
      ψ.hom.base '' connectedComponentIn
          ((pullback.fst (baseChange R c A) s₂ ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
              (pullback (baseChange R c A) s₂).Opens) : Set ↥(pullback (baseChange R c A) s₂))
          (((sectionFibrePoint (sectionBaseChange A ε) s₂).1).base (IsLocalRing.closedPoint K)) =
        connectedComponentIn ((pullback.fst c sb ⁻¹ᵁ U : (pullback c sb).Opens) : Set ↥(pullback c sb))
          (((sectionFibrePoint ε sb).1).base (IsLocalRing.closedPoint K)) :=
    ⟨pullbackLeftPullbackSndIso c (specMap R A) s₂, pullbackLeftPullbackSndIso_hom_snd _ _ _,
      pullbackLeftPullbackSndIso_hom_fst _ _ _,
      sectionFibrePoint_sectionBaseChange_comp_pullbackLeftPullbackSndIso_hom c ε A s₂,
      image_connectedComponentIn_sectionFibrePoint c ε A s₂ U⟩
  obtain ⟨φ₁, hφ₁snd, hφ₁fst⟩ : ∃ φ₁ : pullback (pullback.snd (baseChange R c A) t) s ≅ pullback (baseChange R c A) s₂,
      φ₁.hom ≫ pullback.snd (baseChange R c A) s₂ = pullback.snd (pullback.snd (baseChange R c A) t) s ∧
      φ₁.hom ≫ pullback.fst (baseChange R c A) s₂ =
        pullback.fst (pullback.snd (baseChange R c A) t) s ≫ pullback.fst (baseChange R c A) t :=
    ⟨pullbackLeftPullbackSndIso (baseChange R c A) t s, pullbackLeftPullbackSndIso_hom_snd _ _ _,
      pullbackLeftPullbackSndIso_hom_fst _ _ _⟩
  obtain ⟨Φ, hΦx, hΦinv⟩ : ∃ Φ : pullback c sb ≅ pullback (pullback.snd (baseChange R c A) t) s,
      Φ.hom ≫ fibreAt (baseChange R c A) t s = pullback.snd c sb ∧ Φ.inv = φ₁.hom ≫ ψ.hom := by
    refine ⟨(φ₁ ≪≫ ψ).symm, ?_, rfl⟩
    rw [Iso.symm_hom, Iso.trans_inv, fibreAt, Category.assoc, Iso.inv_comp_eq, hψsnd, Iso.inv_comp_eq, hφ₁snd]

  have hnsb : ¬ Smooth (pullback.snd c sb) := by
    intro h
    apply hns
    have : Smooth (ψ.hom ≫ pullback.snd c sb) := inferInstance
    rwa [hψsnd] at this

  haveI : IsReduced (pullback c sb) := hgred K sb
  obtain ⟨M₁, M₂, i₁, i₂, hci₁, hci₂, n, a, b, 𝒲₀, hi₁, hi₂, hcover, ha, hnode, hinter, htrans, hU0₁, hU0₂, hU1₁, hU1₂,
    hεinf, hcomp, hnodesU, hnonnodes, W₁, hW₁eq, hW₁oi⟩ := hbad K sb hnsb
  haveI := hci₁
  haveI := hci₂
  haveI := hW₁oi

  obtain rfl : n = g + 1 := by
    let φP : pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) sb ≅ pullback c sb :=
      pullbackLeftPullbackSndIso c (𝟙 _) sb ≪≫ pullback.congrHom rfl (Category.comp_id sb)
    have hφP : φP.hom ≫ pullback.snd c sb = fibreAt c (𝟙 _) sb := by
      simp only [φP, fibreAt, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd]
    obtain ⟨𝒱', -, -, ⟨h0⟩, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c (𝟙 _) sb) (pullback.snd c sb) φP hφP 𝒲₀ (SheafOfModules.unit (pullback c sb).ringCatSheaf)
      (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) sb).ringCatSheaf)
      (Scheme.Modules.pullbackTensorUnitObjIso φP.hom).symm
    refine TwoGluedProjectiveLines.eq_finrank_H1_add_one_of_finrank_H0_eq_one K (pullback.snd c sb) M₁ M₂ i₁ i₂
      hi₁ hi₂ hcover a b ha hnode hinter htrans 𝒲₀ hU0₁ hU0₂ hU1₁ hU1₂ g ?_ ?_
    · rw [← h0.finrank_eq]
      exact Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections c hH0 (𝟙 _) K sb 𝒱'
    · rw [← h1.finrank_eq]
      exact hg K sb 𝒱'

  obtain ⟨𝒲₀', -, -, hi₁', hi₂', hcover', hnode', hinter', htrans', hU0₁', hU0₂', hU1₁', hU1₂', hoi', hW₁img, hri₁, -⟩ :=
    TwoGluedProjectiveLines.exists_twoAffineOpenCover_presentation_comp_iso (pullback.snd c sb)
      (fibreAt (baseChange R c A) t s) Φ hΦx M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b hnode hinter htrans 𝒲₀ hU0₁ hU0₂ hU1₁ hU1₂ W₁
  haveI := hoi'

  haveI : IsAffineHom i₁ := inferInstance
  haveI : IsAffineHom i₂ := inferInstance
  let 𝒱₁ : M₁.C.TwoAffineOpenCover :=
    { U0 := i₁ ⁻¹ᵁ 𝒲₀.U0
      U1 := i₁ ⁻¹ᵁ 𝒲₀.U1
      isAffineOpen_U0 := 𝒲₀.isAffineOpen_U0.preimage _
      isAffineOpen_U1 := 𝒲₀.isAffineOpen_U1.preimage _
      sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲₀.sup_eq_top]; rfl
      isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲₀.isAffineOpen_inf.preimage _ }
  let 𝒱₂ : M₂.C.TwoAffineOpenCover :=
    { U0 := i₂ ⁻¹ᵁ 𝒲₀.U0
      U1 := i₂ ⁻¹ᵁ 𝒲₀.U1
      isAffineOpen_U0 := 𝒲₀.isAffineOpen_U0.preimage _
      isAffineOpen_U1 := 𝒲₀.isAffineOpen_U1.preimage _
      sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲₀.sup_eq_top]; rfl
      isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲₀.isAffineOpen_inf.preimage _ }

  have heM : e ≤ M := le_of_lt (lt_of_le_of_lt (Nat.le_add_left e _) hMlt)
  let i₀ : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))) :=
    ⟨⟨⟨Fin.castLE heM, Fin.castLE_injective heM⟩, fun i => ⟨0, hdeg i⟩⟩⟩
  haveI : SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) :=
    smoothOfRelativeDimension_one_preimage_comp_baseChange c U A
  have hεUA : Set.range (sectionBaseChange A ε).1 ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) :=
    range_sectionBaseChange_subset_preimage c ε U hεA A
  have hDUA : ((Dγ i₀).pullbackAlong t (Category.comp_id t)).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) :=
    (hDγU i₀).pullbackAlong t (Category.comp_id t)
  haveI : IsReduced (pullback (pullback.snd (baseChange R c A) t) s) := isReduced_of_isOpenImmersion Φ.inv
  haveI : IsSeparated (fibreAt (baseChange R c A) t s) := by rw [fibreAt]; infer_instance

  have hDTinv : ((Dγ i₀).pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn _ _ hDUA
  have hinv : Scheme.Modules.IsInvertible (fibreModule (baseChange R c A) t s
      (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗
        ((Dγ i₀).pullbackAlong t (Category.comp_id t)).idealModule))) :=
    (L.isInvertible.tensor ((((isInvertible_sectionIdeal_of_range_subset (baseChange R c A) (sectionBaseChange A ε)
      _ hεUA t).pow r).isInvertible_invModule).tensor hDTinv.isInvertible_module)).pullback _

  have hW₁ri₁ : (W₁ : Set ↥(pullback c sb)) ⊆ Set.range i₁.base := by
    rw [hW₁eq]
    intro x hx
    exact (Set.eq_univ_iff_forall.mp hcover x).resolve_right hx
  have hW₁' : ((Φ.inv ⁻¹ᵁ W₁ : (pullback (pullback.snd (baseChange R c A) t) s).Opens) :
      Set ↥(pullback (pullback.snd (baseChange R c A) t) s)) ⊆ Set.range (i₁ ≫ Φ.hom).base := by
    rw [hW₁img, hri₁]
    exact Set.image_mono hW₁ri₁

  have hoff : ∀ x : ↥(pullback c sb), x ∈ Set.range i₁.base →
      x ∈ ((pullback.fst c sb ⁻¹ᵁ U : (pullback c sb).Opens) : Set ↥(pullback c sb)) → x ∈ (W₁ : Set ↥(pullback c sb)) := by
    rintro x ⟨p, rfl⟩ hxU
    rw [hW₁eq]
    rintro ⟨q, hq⟩
    obtain ⟨j, rfl, -⟩ := hinter p q hq.symm
    exact hnodesU j hxU

  have hD' : ∀ y : ↥(pullback (pullback.snd (baseChange R c A) t) s),
      (pullback.fst (pullback.snd (baseChange R c A) t) s).base y ∈
        ((Dγ i₀).pullbackAlong t (Category.comp_id t)).I.support → y ∈ Φ.inv ⁻¹ᵁ W₁ := by
    intro y hy
    change (pullback.fst (pullback.snd (baseChange R c A) t) s).base y ∈
      (((Dγ i₀).I.comap (mapOnProdOver (baseChange R c A) t (Category.comp_id t))).support :
        Set ↥(pullback (baseChange R c A) t)) at hy
    rw [Scheme.IdealSheafData.support_comap] at hy
    change (mapOnProdOver (baseChange R c A) t (Category.comp_id t)).base
        ((pullback.fst (pullback.snd (baseChange R c A) t) s).base y) ∈
      ((Dγ i₀).I.support : Set ↥(pullback (baseChange R c A) (𝟙 _))) at hy
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨w, hw⟩ := hy
    have himg : (pullback.fst (baseChange R c A) s₂).base (φ₁.hom.base y) ∈
        ((Dγ i₀).I.subschemeι ≫ pullback.fst (baseChange R c A) (𝟙 _)).base '' Set.univ := by
      refine ⟨w, trivial, ?_⟩
      have h2 := congrArg (fun f : pullback (pullback.snd (baseChange R c A) t) s ⟶ pullback c (specMap R A) => f.base y) hφ₁fst
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h2
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hw, ← Scheme.Hom.comp_apply, mapOnProdOver_fst, h2]
    have hA2 := preimage_support_prodKerGraph_subset_connectedComponentIn_of_blocks c ε U A B deg z hzε σ hσfac
      i₀.down.1.1 i₀.down.2 (Dγ i₀) (hDγI i₀) K s₂ hns himg
    have hyb : ψ.hom.base (φ₁.hom.base y) ∈
        connectedComponentIn ((pullback.fst c sb ⁻¹ᵁ U : (pullback c sb).Opens) : Set ↥(pullback c sb))
          (((sectionFibrePoint ε sb).1).base (IsLocalRing.closedPoint K)) := by
      rw [← hψcomp]
      exact ⟨_, hA2, rfl⟩
    rw [← hcomp] at hyb
    have hmem := hoff _ hyb.1 hyb.2
    change Φ.inv.base y ∈ (W₁ : Set ↥(pullback c sb))
    rwa [hΦinv, Scheme.Hom.comp_apply]

  have hrs : (s ≫ rigSection (baseChange R c A) t (sectionBaseChange A ε)) ≫ pullback.snd (baseChange R c A) t = 𝟙 _ ≫ s := by
    rw [Category.assoc, rigSection, pullback.lift_snd, Category.comp_id, Category.id_comp]
  have hε' : ∀ y : ↥(pullback (pullback.snd (baseChange R c A) t) s),
      (pullback.fst (pullback.snd (baseChange R c A) t) s).base y ∈
        Set.range (rigSection (baseChange R c A) t (sectionBaseChange A ε)).base → y ∈ Φ.inv ⁻¹ᵁ W₁ := by
    intro y hy
    obtain rfl := eq_of_fst_mem_range_rigSection (baseChange R c A) t (sectionBaseChange A ε) s
      (pullback.lift _ _ hrs) (pullback.lift_fst _ _ _) y hy

    have heψ : pullback.lift _ _ hrs ≫ φ₁.hom ≫ ψ.hom = (sectionFibrePoint ε sb).1 := by
      rw [← hψε, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, hφ₁fst, pullback.lift_fst_assoc, Category.assoc]
        simp only [rigSection, sectionFibrePoint, pullback.lift_fst]
        rw [hs₂, Category.assoc]
      · rw [Category.assoc, hφ₁snd, pullback.lift_snd]
        simp only [sectionFibrePoint, pullback.lift_snd]
    change Φ.inv.base _ ∈ (W₁ : Set ↥(pullback c sb))
    rw [hΦinv, ← Scheme.Hom.comp_apply, heψ]
    refine hoff _ ⟨_, hεinf⟩ ?_
    change (pullback.fst c sb).base (((sectionFibrePoint ε sb).1).base (IsLocalRing.closedPoint K)) ∈ (U : Set C)
    rw [← Scheme.Hom.comp_apply]
    simp only [sectionFibrePoint, pullback.lift_fst]
    exact hεA ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

  have hback : ∀ y : M₂.C, (i₂ ≫ Φ.hom).base y ∉ Φ.inv ⁻¹ᵁ W₁ := by
    intro y hy
    change Φ.inv.base ((i₂ ≫ Φ.hom).base y) ∈ (W₁ : Set ↥(pullback c sb)) at hy
    rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id, hW₁eq] at hy
    exact hy ⟨y, rfl⟩
  have hD₂' : ∀ y : M₂.C, (pullback.fst (pullback.snd (baseChange R c A) t) s).base ((i₂ ≫ Φ.hom).base y) ∉
      ((Dγ i₀).pullbackAlong t (Category.comp_id t)).I.support :=
    fun y hy => hback y (hD' _ hy)
  have hε₂' : ∀ y : M₂.C, (pullback.fst (pullback.snd (baseChange R c A) t) s).base ((i₂ ≫ Φ.hom).base y) ∉
      Set.range (rigSection (baseChange R c A) t (sectionBaseChange A ε)).base :=
    fun y hy => hback y (hε' _ hy)

  exact ⟨i₀, fun 𝒲 => (subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines A (baseChange R c A)
    (pullback.fst c (specMap R A) ⁻¹ᵁ U) (sectionBaseChange A ε) hεUA t ((Dγ i₀).pullbackAlong t (Category.comp_id t))
    hDUA s M₁ M₂ (i₁ ≫ Φ.hom) (i₂ ≫ Φ.hom) hi₁' hi₂' hcover' g a b ha hnode' hinter' htrans' 𝒲₀' hU0₁' hU0₂' hU1₁' hU1₂'
    𝒱₁ 𝒱₂ (Φ.inv ⁻¹ᵁ W₁) hW₁' hD' hε' hD₂' hε₂' hr L hL hinv 𝒲).1⟩

end S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth (solution)
