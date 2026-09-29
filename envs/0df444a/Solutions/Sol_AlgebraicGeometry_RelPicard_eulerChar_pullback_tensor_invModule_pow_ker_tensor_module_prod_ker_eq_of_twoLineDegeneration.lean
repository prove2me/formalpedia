-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7af44534-a1f6-5314-a6b6-1dfb2d24436c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicCurve"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (e r : ℕ) (g : ℕ) (hr : g + e = r)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
    (n : ℕ) (a b : Fin n → kˣ)
    (hi₁ : i₁ ≫ pullback.snd c s = M₁.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hεinf : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))
    (hcomp : Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hnodesU : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (W₁ : (pullback c s).Opens) (hW₁eq : (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ)
    [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]

    (v : Fin e → {q : Spec (CommRingCat.of k) ⟶ pullback c s // q ≫ pullback.snd c s = 𝟙 _})
    (hvcomp : ∀ j, ((v j).1).base (IsLocalRing.closedPoint k) ∈
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (L₀ : (pullback c s).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (hL₀₁ : Nonempty ((Scheme.Modules.pullback i₁).obj L₀ ≅
        (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit (pullback c s).ringCatSheaf))) :
    ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (L₀ ⊗ ((((sectionFibrePoint ε s).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)))).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (L₀ ⊗ ((((sectionFibrePoint ε s).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)))).H1 = g + 1 := by
  intro 𝒲'
  classical

  have hva : ∀ j, ((v j).1 ≫ pullback.fst c s) ≫ c = s := fun j => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, (v j).2, Category.id_comp]
  have hvpt : ∀ j (x : ↥(Spec (CommRingCat.of k))), ((v j).1).base x = ((v j).1).base (IsLocalRing.closedPoint k) :=
    fun j x => by rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
  have hvU : ∀ j, Set.range ((v j).1 ≫ pullback.fst c s).base ⊆ (U : Set C) := by
    intro j
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, hvpt j x]
    have hm := connectedComponentIn_subset _ _ (hvcomp j)
    exact hm
  obtain ⟨D, hDI, hDU⟩ := AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
    (f := c) U (T := Spec (CommRingCat.of k)) (g := s) (fun j => (v j).1 ≫ pullback.fst c s) hva hvU
  have hgraph : ∀ j, graphOver c ((v j).1 ≫ pullback.fst c s) (hva j) = (v j).1 := fun j => by
    apply pullback.hom_ext
    · rw [graphOver_fst]
    · rw [graphOver_snd, (v j).2]
  have hDI' : D.I = ∏ j, (v j).1.ker := by
    rw [hDI, prodKerGraph_eq_prod]
    exact Finset.prod_congr rfl (fun j _ => by rw [hgraph j])

  haveI hvci : ∀ j, IsClosedImmersion (v j).1 := fun j => by rw [← hgraph j]; infer_instance

  have hDsupp : ∀ x : ↥(pullback c s), x ∈ (D.I.support : Set ↥(pullback c s)) → ∃ j, x ∈ Set.range ((v j).1).base := by
    intro x hx
    rw [hDI'] at hx
    have key : ∀ (S : Finset (Fin e)), x ∈ ((∏ j ∈ S, (v j).1.ker).support : Set ↥(pullback c s)) →
        ∃ j, x ∈ Set.range ((v j).1).base := by
      intro S
      induction S using Finset.cons_induction with
      | empty =>
        intro h
        rw [Finset.prod_empty] at h
        change x ∈ ((⊤ : (pullback c s).IdealSheafData).support : Set ↥(pullback c s)) at h
        rw [Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot] at h
        simp at h
      | cons i S hi ih =>
        intro h
        rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, Set.mem_union] at h
        rcases h with h | h
        · refine ⟨i, ?_⟩
          have h' : x ∈ closure (Set.range ((v i).1).base) := by
            rw [← Scheme.Hom.support_ker]; exact h
          rwa [(v i).1.isClosedEmbedding.isClosed_range.closure_eq] at h'
        · exact ih h
    exact key Finset.univ hx

  let F := pullback (pullback.snd c s) (𝟙 (Spec (CommRingCat.of k)))
  let φ : F ≅ pullback c s := asIso (pullback.fst (pullback.snd c s) (𝟙 (Spec (CommRingCat.of k))))
  have hφsnd : φ.hom ≫ pullback.snd c s = fibreAt c s (𝟙 _) := by
    change pullback.fst _ _ ≫ _ = pullback.snd _ _
    rw [pullback.condition, Category.comp_id]
  have hφinv : φ.inv ≫ fibreAt c s (𝟙 _) = pullback.snd c s := by
    rw [← hφsnd, φ.inv_hom_id_assoc]
  have hφy : ∀ y : ↥F, φ.inv.base (φ.hom.base y) = y := fun y => by
    change (φ.hom ≫ φ.inv).base y = y; rw [φ.hom_inv_id]; rfl

  let i₁' : M₁.C ⟶ F := i₁ ≫ φ.inv
  have hi₁' : i₁' ≫ fibreAt c s (𝟙 _) = M₁.toBase := by
    change (i₁ ≫ φ.inv) ≫ _ = _
    rw [Category.assoc, hφinv, hi₁]
  have hi₁'φ : i₁' ≫ pullback.fst (pullback.snd c s) (𝟙 _) = i₁ := by
    change (i₁ ≫ φ.inv) ≫ φ.hom = i₁; rw [Category.assoc, φ.inv_hom_id, Category.comp_id]

  let W₁' : F.Opens := φ.hom ⁻¹ᵁ W₁
  have hO : i₁' ⁻¹ᵁ W₁' = i₁ ⁻¹ᵁ W₁ := by
    change (i₁ ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₁) = _
    rw [← Scheme.Hom.comp_preimage, Category.assoc, φ.inv_hom_id, Category.comp_id]
  haveI : IsOpenImmersion ((i₁' ⁻¹ᵁ W₁').ι ≫ i₁') := by
    have : (i₁' ⁻¹ᵁ W₁').ι ≫ i₁' = (M₁.C.isoOfEq hO).hom ≫ ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁) ≫ φ.inv := by
      rw [Category.assoc, ← Category.assoc (M₁.C.isoOfEq hO).hom, Scheme.isoOfEq_hom_ι]
    rw [this]; infer_instance

  have hnotU : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      i₁.base p ∉ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) := by
    intro p q h
    obtain ⟨i, rfl, -⟩ := hinter p q h
    exact hnodesU i

  have hW₁range : (W₁ : Set ↥(pullback c s)) ⊆ Set.range i₁.base := by
    intro y hy
    rw [hW₁eq] at hy
    rcases (Set.eq_univ_iff_forall.mp hcover y) with h | h
    · exact h
    · exact absurd h hy
  have hmemW₁ : ∀ z : ↥(pullback c s), z ∈ Set.range i₁.base → z ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) → z ∈ W₁ := by
    intro z hz hzU
    change z ∈ (W₁ : Set ↥(pullback c s))
    rw [hW₁eq]
    rintro ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hz
    exact hnotU p q hp (hp ▸ hzU)
  have hW₁' : (W₁' : Set ↥F) ⊆ Set.range i₁'.base := by
    intro y hy
    obtain ⟨p, hp⟩ := hW₁range hy
    exact ⟨p, by change φ.inv.base (i₁.base p) = y; rw [hp, hφy]⟩

  have hcc : connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
      (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ⊆ (W₁ : Set ↥(pullback c s)) := by
    intro z hz
    have hzU : z ∈ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) :=
      connectedComponentIn_subset _ _ hz
    have hz1 : z ∈ Set.range i₁.base := by
      have : z ∈ Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) := by
        rw [hcomp]; exact hz
      exact this.1
    exact hmemW₁ z hz1 hzU

  have hD' : ∀ y : ↥F, (pullback.fst (pullback.snd c s) (𝟙 _)).base y ∈ D.I.support → y ∈ W₁' := by
    intro y hy
    change φ.hom.base y ∈ (W₁ : Set ↥(pullback c s))
    obtain ⟨j, x, hx⟩ := hDsupp _ hy
    have hyx : φ.hom.base y = ((v j).1).base (IsLocalRing.closedPoint k) := by
      show (pullback.fst (pullback.snd c s) (𝟙 _)).base y = _
      rw [← hx, hvpt j x]
    rw [hyx]
    exact hcc (hvcomp j)

  have hε' : ∀ y : ↥F, (pullback.fst (pullback.snd c s) (𝟙 _)).base y ∈ Set.range (rigSection c s ε).base → y ∈ W₁' := by
    rintro y ⟨q, hq⟩
    change φ.hom.base y ∈ (W₁ : Set ↥(pullback c s))
    have hq' : φ.hom.base y = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) := by
      rw [Subsingleton.elim q (IsLocalRing.closedPoint k)] at hq; exact hq.symm
    rw [hq']
    refine hmemW₁ _ ⟨_, hεinf⟩ ?_
    change (pullback.fst c s).base (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∈ (U : Set C)
    rw [← Scheme.Hom.comp_apply, show (sectionFibrePoint ε s).1 ≫ pullback.fst c s = s ≫ ε.1 from pullback.lift_fst _ _ _]
    exact hεU ⟨_, rfl⟩

  have hLL₁ : ∀ 𝒲'' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲''.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁').obj
          (fibreModule c s (𝟙 _) L₀))).H0 : ℤ) -
        Module.finrank k (𝒲''.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁').obj
          (fibreModule c s (𝟙 _) L₀))).H1 = 1 := by
    intro 𝒲''
    have eU : (Scheme.Modules.pullback i₁').obj (fibreModule c s (𝟙 _) L₀) ≅
        (Scheme.Modules.pullback (Iso.refl M₁.C).hom).obj (SheafOfModules.unit M₁.C.ringCatSheaf : M₁.C.Modules) :=
      (Scheme.Modules.pullbackComp i₁' (pullback.fst (pullback.snd c s) (𝟙 _))).app L₀ ≪≫
        (Scheme.Modules.pullbackCongr hi₁'φ).app L₀ ≪≫ hL₀₁.some ≪≫
        Scheme.Modules.pullbackUnitIso i₁ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm
    obtain ⟨𝒱, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso M₁.toBase M₁.toBase
      (Iso.refl M₁.C) (Category.id_comp _) 𝒲'' _ _ eU
    have h𝒱 : 𝒱 = 𝒲'' := by
      cases 𝒱; cases 𝒲''; simp only at h0 h1; subst h0; subst h1; rfl
    subst h𝒱
    obtain ⟨hH1, hH0⟩ := AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₁ 𝒱
    rw [e0.finrank_eq, e1.finrank_eq, hH0, hH1]; norm_num

  have key := AlgebraicGeometry.RelPicard.eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq R c U ε hεU s D
    hDU (𝟙 _) M₁ i₁' hi₁' W₁' hW₁' hD' hε' L₀ hL₀ hLL₁ g (g + 1) hr rfl

  set Y := L₀ ⊗ (sectionTwist c ε s r ⊗ D.idealModule) with hY
  have eY : (Scheme.Modules.pullback i₁').obj (fibreModule c s (𝟙 _) Y) ≅
      (Scheme.Modules.pullback (Iso.refl M₁.C).hom).obj ((Scheme.Modules.pullback i₁).obj
        (L₀ ⊗ ((((sectionFibrePoint ε s).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module))) := by
    refine ((Scheme.Modules.pullbackComp i₁' (pullback.fst (pullback.snd c s) (𝟙 _))).app Y) ≪≫ ?_
    refine (Scheme.Modules.pullbackCongr hi₁'φ).app Y ≪≫ ?_
    refine ?_ ≪≫ ((Scheme.Modules.pullbackId _).app _).symm ≪≫ ((Scheme.Modules.pullbackCongr rfl).app _)
    refine (Scheme.Modules.pullback i₁).mapIso (eqToIso ?_)
    change L₀ ⊗ (sectionTwist c ε s r ⊗ D.I.module) = _
    rw [hDI']
    rfl
  obtain ⟨𝒱, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso M₁.toBase M₁.toBase
    (Iso.refl M₁.C) (Category.id_comp _) 𝒲' _ _ eY
  have h𝒱 : 𝒱 = 𝒲' := by
    cases 𝒱; cases 𝒲'; simp only at h0 h1; subst h0; subst h1; rfl
  subst h𝒱
  rw [← e0.finrank_eq, ← e1.finrank_eq]
  exact_mod_cast key 𝒱

end S_AlgebraicGeometry_RelPicard_eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_pullback_tensor_invModule_pow_ker_tensor_module_prod_ker_eq_of_twoLineDegeneration (solution)
