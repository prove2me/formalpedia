-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c07c0e8a-baa4-5deb-a4c2-ee45873f9096

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverPreimage
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_eq_finrank_H1_add_one_of_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
import Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II"
p2m_attr_erase "instance" "DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicCurve AlgebraicGeometry.SmoothProperCurve TensorProduct"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b)
    (r g : ℕ) (hr : 2 * g ≤ r + 1) (hcount : r * b ^ (r - g) + (r - g) < M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i))
    [IsProper (pullback.snd c (SmoothProperCurve.specMap R Ω))]
    [IsReduced (pullback c (SmoothProperCurve.specMap R Ω))]

    (hns : ¬ Smooth (pullback.snd c (SmoothProperCurve.specMap R Ω)))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))
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

    (hzε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base ⊆
      connectedComponentIn
        (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (hH0 : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω ↥(𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H0 = 1)
    (hg : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H1 = g)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a : Fin (r - g) → Fin M, Function.Injective a ∧
      ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
              (∏ j, (v j).1.ker).module))).H1 := by
  classical
  haveI : DecidableEq (RatFunc Ω) := Classical.decEq _

  have hle : r - g ≤ M := by
    have h1 : r - g ≤ r * b ^ (r - g) + (r - g) := Nat.le_add_left _ _
    omega
  refine ⟨Fin.castLE hle, Fin.castLE_injective hle, fun v hv 𝒲 => ?_⟩

  obtain ⟨M₁, M₂, i₁, i₂, hci₁, hci₂, n, na, nb, 𝒲₀, hi₁, hi₂, hcover, hna, hnode, hinter, htrans,
    hU0₁, hU0₂, hU1₁, hU1₂, hεinf, hcomp, hnodesU, hnonnodes, W₁, hW₁eq, hW₁imm⟩ := hbad Ω (SmoothProperCurve.specMap R Ω) hns
  haveI := hci₁; haveI := hci₂; haveI := hW₁imm

  have hn : n = g + 1 :=
    AlgebraicGeometry.TwoGluedProjectiveLines.eq_finrank_H1_add_one_of_finrank_H0_eq_one Ω (pullback.snd c (SmoothProperCurve.specMap R Ω))
      M₁ M₂ i₁ i₂ hi₁ hi₂ hcover na nb hna hnode hinter htrans 𝒲₀ hU0₁ hU0₂ hU1₁ hU1₂ g (hH0 𝒲₀) (hg 𝒲₀)

  have hnotU : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q → i₁.base p ∉ (pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) := by
    intro p q h
    obtain ⟨i, rfl, -⟩ := hinter p q h
    exact hnodesU i
  have hmemW₁ : ∀ y : ↥(pullback c (SmoothProperCurve.specMap R Ω)), y ∈ Set.range i₁.base → y ∈ (pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) → y ∈ W₁ := by
    intro y hy hyU
    change y ∈ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
    rw [hW₁eq]
    rintro ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hy
    exact hnotU p q hp (hp ▸ hyU)
  have hcc : connectedComponentIn ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
      (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) ⊆ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    intro y hy
    have hyU : y ∈ ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := connectedComponentIn_subset _ _ hy
    have hy1 : y ∈ Set.range i₁.base := by
      have : y ∈ Set.range i₁.base ∩ ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by rw [hcomp]; exact hy
      exact this.1
    exact hmemW₁ y hy1 hyU

  have hvcomp : ∀ j, ((v j).1).base (IsLocalRing.closedPoint Ω) ∈
      connectedComponentIn ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) := by
    intro j
    obtain ⟨ψ, hψ⟩ := hv j
    apply hzε (Fin.castLE hle j)
    show (pullback.fst c (SmoothProperCurve.specMap R Ω)).base (((v j).1).base (IsLocalRing.closedPoint Ω)) ∈ Set.range (z (Fin.castLE hle j)).base
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hvU : ∀ j, ((v j).1).base (IsLocalRing.closedPoint Ω) ∈ (pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) :=
    fun j => connectedComponentIn_subset _ _ (hvcomp j)
  have hvW : ∀ j, ((v j).1).base (IsLocalRing.closedPoint Ω) ∈ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := fun j => hcc (hvcomp j)
  have hεcomp : ((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω) ∈ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    refine hmemW₁ _ ⟨_, hεinf⟩ ?_
    show (pullback.fst c (SmoothProperCurve.specMap R Ω)).base (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) ∈ (U : Set C)
    rw [← Scheme.Hom.comp_apply, show (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = (SmoothProperCurve.specMap R Ω) ≫ ε.1 from pullback.lift_fst _ _ _]
    exact hεU ⟨_, rfl⟩

  obtain ⟨hL₀₁, hχ₁⟩ :=
    AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
      Ω (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ hL₀ h0 M₁ i₁ hi₁ (𝒲₀.preimage i₁)
      (AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc Ω M₁)
  obtain ⟨hL₀₂, -⟩ :=
    AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
      Ω (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ hL₀ h0 M₂ i₂ hi₂ (𝒲₀.preimage i₂)
      (AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc Ω M₂)

  let J : (pullback c (SmoothProperCurve.specMap R Ω)).IdealSheafData := (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker
  have hJdef : J = sectionIdeal c ε (SmoothProperCurve.specMap R Ω) := rfl
  have hJ : J.IsInvertible := by rw [hJdef]; exact isInvertible_sectionIdeal_of_range_subset c ε U hεU _
  obtain ⟨D, hDI, hDU⟩ := AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
    (f := c) U (g := (SmoothProperCurve.specMap R Ω)) (fun j => (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω))
    (fun j => by rw [Category.assoc, pullback.condition, ← Category.assoc, (v j).2, Category.id_comp])
    (fun j => by
      rintro _ ⟨x, rfl⟩
      rw [Subsingleton.elim x (IsLocalRing.closedPoint Ω), Scheme.Hom.comp_apply]
      exact hvU j)
  have hDI' : D.I = ∏ j, (v j).1.ker := by
    rw [hDI, prodKerGraph_eq_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    apply pullback.hom_ext
    · rw [graphOver_fst]
    · rw [graphOver_snd, (v j).2]
  have hN : (∏ j, (v j).1.ker).IsInvertible := hDI' ▸ D.isInvertible_I_of_supportedIn U hDU

  haveI : IsSeparated (pullback.snd c (SmoothProperCurve.specMap R Ω)) := inferInstance
  have hclosed : ∀ (q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω)), q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _ → IsClosedImmersion q := by
    intro q hq
    haveI : IsClosedImmersion (q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω)) := by rw [hq]; infer_instance
    exact IsClosedImmersion.of_comp q (pullback.snd c (SmoothProperCurve.specMap R Ω))
  have hsuppker : ∀ (q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω)), q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _ →
      (q.ker.support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) = {q.base (IsLocalRing.closedPoint Ω)} := by
    intro q hq
    haveI := hclosed q hq
    rw [Scheme.Hom.support_ker, q.isClosedEmbedding.isClosed_range.closure_eq]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Subsingleton.elim x (IsLocalRing.closedPoint Ω)]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  have hW₁i₂ : ∀ y : M₂.C, i₂.base y ∉ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    intro y hy
    rw [hW₁eq] at hy
    exact hy ⟨y, rfl⟩
  have hJsupp : ∀ y : M₂.C, i₂.base y ∉ (J.support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    intro y hy
    rw [hsuppker _ (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).2, Set.mem_singleton_iff] at hy
    exact hW₁i₂ y (hy ▸ hεcomp)
  have hsuppN : ((∏ j, (v j).1.ker).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    classical
    refine Finset.prod_induction (fun j => (v j).1.ker) (fun I => (I.support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆ (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) ?_ ?_ ?_
    · intro I I' hI hI'
      rw [Scheme.IdealSheafData.support_mul]
      rintro y (hy | hy)
      exacts [hI hy, hI' hy]
    · show ((1 : (pullback c (SmoothProperCurve.specMap R Ω)).IdealSheafData).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆ _
      rw [show (1 : (pullback c (SmoothProperCurve.specMap R Ω)).IdealSheafData) = ⊤ from rfl, Scheme.IdealSheafData.support_top]
      intro y hy
      exact absurd hy (by simp)
    · intro j _
      rw [hsuppker _ (v j).2]
      rintro y rfl
      exact hvW j
  have hNsupp : ∀ y : M₂.C, i₂.base y ∉ ((∏ j, (v j).1.ker).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) :=
    fun y hy => hW₁i₂ y (hsuppN hy)

  have hL₂ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
    i₂ J hJ (∏ j, (v j).1.ker) hN r hJsupp hNsupp L₀ hL₀₂
  have hL₁ : ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank Ω ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (L₀ ⊗ ((J ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)))).H0 : ℤ) -
        Module.finrank Ω (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (L₀ ⊗ ((J ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)))).H1 = n := by
    rw [hn]
    intro 𝒲'
    exact AlgebraicGeometry.RelPicard.eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
      R c U ε hεU (r - g) r g (by omega) Ω (SmoothProperCurve.specMap R Ω) M₁ M₂ i₁ i₂ n na nb hi₁ hcover hinter hεinf hcomp
      hnodesU W₁ hW₁eq v hvcomp L₀ hL₀ hL₀₁ 𝒲'

  have hLinv : Scheme.Modules.IsInvertible (L₀ ⊗ ((J ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)) :=
    hL₀.tensor ((hJ.pow r).isInvertible_invModule.tensor hN.isInvertible_module)
  haveI : IsSeparated (pullback.snd c (SmoothProperCurve.specMap R Ω)) := inferInstance
  exact (AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed
    Ω (pullback.snd c (SmoothProperCurve.specMap R Ω)) M₁ M₂ i₁ i₂ hi₁ hi₂ hcover na nb hna hnode hinter htrans 𝒲₀ hU0₁ hU0₂ hU1₁ hU1₂
    (L₀ ⊗ ((J ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)) hLinv hL₂ hL₁ 𝒲).2

end S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus (solution)
