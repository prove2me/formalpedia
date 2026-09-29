-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e2ad58a3-7cbd-5730-b06a-4f7ddfdcae11

import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections
import Theorems.Thm_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_eulerChar_sectionsOf_invModule_pow_ker_tensor_module_prod_ker_eq
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoAffineOpenCover_mem_of_isAlgClosed
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
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one"
p2m_attr_erase "simp" "GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~genus"

namespace E86HGPA

open scoped TensorProduct

theorem nonempty_algHom_of_faithfullyFlat (R A Ω : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.FaithfullyFlat R A] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] :
    Nonempty (A →ₐ[R] Ω) := by
  classical

  haveI : Nontrivial (Ω ⊗[R] A) := Module.FaithfullyFlat.rTensor_nontrivial R A Ω
  haveI : Module.Finite Ω (Ω ⊗[R] A) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω ⊗[R] A)
  haveI := hm

  haveI : Module.Finite Ω ((Ω ⊗[R] A) ⧸ m) := inferInstance
  haveI : Algebra.IsIntegral Ω ((Ω ⊗[R] A) ⧸ m) := Algebra.IsIntegral.of_finite Ω _
  have hbij : Function.Bijective (algebraMap Ω ((Ω ⊗[R] A) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ((Ω ⊗[R] A) ⧸ m) ≃ₐ[Ω] Ω := (AlgEquiv.ofBijective (Algebra.ofId Ω ((Ω ⊗[R] A) ⧸ m)) hbij).symm
  exact ⟨(e.restrictScalars R).toAlgHom.comp
    ((Ideal.Quotient.mkₐ R m).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)))⟩

theorem hH0_baseChange {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
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

theorem finrank_sectionsOf_unit_fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    (g : ℕ) {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hg : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H0 = 1 ∧
    Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H1 = g := by

  obtain ⟨φ, hφsnd, -, -⟩ := exists_fibreIso_hom_comp_eq c (𝟙 (Spec (CommRingCat.of R))) x x (Category.comp_id x)

  let e : SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf ≅
      (Scheme.Modules.pullback φ.hom).obj (SheafOfModules.unit (pullback c x).ringCatSheaf) :=
    (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  obtain ⟨𝒲, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) x) (pullback.snd c x) φ hφsnd 𝒱 (SheafOfModules.unit (pullback c x).ringCatSheaf)
    (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf) e
  refine ⟨?_, ?_⟩
  · rw [← e0.finrank_eq]
    exact Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections c hH0 (𝟙 _) k x 𝒲
  · rw [← e1.finrank_eq]
    exact hg 𝒲

theorem smoothOfRelativeDimension_one_snd_of_range_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hU : Set.range (pullback.fst c x).base ⊆ (U : Set C)) :
    SmoothOfRelativeDimension 1 (pullback.snd c x) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  set j := pullback.map (U.ι ≫ c) x c x U.ι (𝟙 _) (𝟙 _) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst c x) ⁻¹' (U : Set C) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  haveI : IsIso j := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [hrange]
    exact hU ⟨z, rfl⟩
  have hjsnd : j ≫ pullback.snd c x = pullback.snd (U.ι ≫ c) x := by
    rw [hj, pullback.lift_snd, Category.comp_id]
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) x) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have : pullback.snd c x = inv j ≫ pullback.snd (U.ι ≫ c) x := by
    rw [← hjsnd, IsIso.inv_hom_id_assoc]
  rw [this]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

theorem isIntegral_pullback_of_smooth
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [GeometricallyConnected c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : Smooth (pullback.snd c x)) : IsIntegral (pullback c x) := by
  haveI := hsm
  haveI : ConnectedSpace ↥(pullback c x) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.snd c x)
  haveI : Nonempty ↥(pullback c x) := ConnectedSpace.toNonempty
  exact isIntegral_of_smooth_of_preconnectedSpace (pullback.snd c x)

end E86HGPA

open E86HGPA

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
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
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (r : ℕ) (hgr : 2 * g ≤ r + 1)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ (r - g) + (r - g) < M) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →
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
  intro Ω _ _ _ L₀ hL₀ h0
  classical

  obtain ⟨t₀⟩ := nonempty_algHom_of_faithfullyFlat R A Ω
  have eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i) := fun i =>
    (AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi (φ i) t₀).some

  have h01 := finrank_sectionsOf_unit_fibre c hH0 g (specMap R Ω) (hg Ω (specMap R Ω))
  haveI : IsReduced (pullback c (specMap R Ω)) := hgred Ω (specMap R Ω)
  by_cases hsm : Smooth (pullback.snd c (specMap R Ω))
  ·
    haveI := hsm
    haveI : GeometricallyConnected c := geometricallyConnected_of_bijective_algebraMap_sections c hH0
    haveI : IsIntegral (pullback c (specMap R Ω)) := isIntegral_pullback_of_smooth c (specMap R Ω) hsm
    haveI : SmoothOfRelativeDimension 1 (pullback.snd c (specMap R Ω)) :=
      smoothOfRelativeDimension_one_snd_of_range_subset c U (specMap R Ω) (hgoodU Ω (specMap R Ω) hsm)
    haveI : GeometricallyIntegral (pullback.snd c (specMap R Ω)) :=
      geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth (baseChange R c Ω) (hH0_baseChange c Ω hH0)
    obtain ⟨𝒱₀, -⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed Ω (pullback.snd c (specMap R Ω))
      (((sectionFibrePoint ε (specMap R Ω)).1).base (IsLocalRing.closedPoint Ω))
    have hg₀ : Module.finrank Ω (𝒱₀.sectionsOf (pullback.snd c (specMap R Ω))
        (𝟙_ (pullback c (specMap R Ω)).Modules)).H1 = g := (h01 𝒱₀).2
    have hgler : g ≤ r := by omega
    have hχ : ∀ (v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) //
          q ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
        (𝒱 : (pullback c (specMap R Ω)).TwoAffineOpenCover),
        (Module.finrank Ω (𝒱.sectionsOf (pullback.snd c (specMap R Ω))
            ((((sectionFibrePoint ε (specMap R Ω)).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H0 : ℤ) -
          Module.finrank Ω (𝒱.sectionsOf (pullback.snd c (specMap R Ω))
            ((((sectionFibrePoint ε (specMap R Ω)).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H1 = 1 := by
      intro v 𝒱
      rw [Scheme.TwoAffineOpenCover.eulerChar_sectionsOf_invModule_pow_ker_tensor_module_prod_ker_eq Ω
        (pullback.snd c (specMap R Ω)) g 𝒱₀ hg₀ (sectionFibrePoint ε (specMap R Ω)).1
        (sectionFibrePoint ε (specMap R Ω)).2 r v 𝒱]
      push_cast [Nat.cast_sub hgler]
      ring
    exact exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre R c ε B z hz hzdisj deg hdeg hdegb
      r g hgr hMlt Ω eB 𝒱₀ hg₀ hχ L₀ hL₀ h0
  ·
    exact exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus R c ε B z hz
      hzdisj deg hdeg hdegb r g hgr hMlt Ω eB hsm U hεA hbad (hzε Ω (specMap R Ω)) (fun 𝒲 => (h01 𝒲).1)
      (fun 𝒲 => (h01 𝒲).2) L₀ hL₀ h0

end S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections (solution)
