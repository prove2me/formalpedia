-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/92496cde-c164-5e3e-98aa-173534c7b800

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
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
import Theorems.Thm_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II"
p2m_attr_erase "instance" "DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard NeronModelInfra"

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard NeronModelInfra"

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage pullbackSpecIso_inv_snd SmoothOfRelativeDimension IsProper Scheme.Hom GeometricallyIntegral GeometricallyIrreducible isPullback_morphismRestrict Spec Spec.map Scheme Smooth pullbackSpecIso IsOpenImmersion Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Hom.comp_apply geometrically Scheme.Modules.IsInvertible RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom prodKerGraph Scheme.Modules.pullbackTensorUnitObjIso RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension RelPicard.isInvertible_sectionIdeal_of_range_subset RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension isInvertible_sectionIdeal_of_range_subset exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth exists_fibreIso_hom_comp_eq exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth"
namespace HCoverASmooth
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

theorem geometricallyIrreducible_snd_of_smooth_of_hH0
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [Smooth (pullback.snd c x)] :
    GeometricallyIrreducible (pullback.snd c x) := by

  letI : Algebra R k := (Spec.preimage x).hom.toAlgebra
  have hx : specMap R k = x := by
    show Spec.map (CommRingCat.ofHom (algebraMap R k)) = x
    conv_rhs => rw [← Spec.map_preimage x]
    rfl

  let e : pullback c x ≅ pullback c (specMap R k) := pullback.congrHom rfl hx.symm
  have hhom : e.hom ≫ pullback.snd c (specMap R k) = pullback.snd c x := by
    simp only [e, pullback.congrHom, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  have hinv : e.inv ≫ pullback.snd c x = pullback.snd c (specMap R k) := by
    rw [← hhom, Iso.inv_hom_id_assoc]

  haveI : Smooth (baseChange R c k) := by
    show Smooth (pullback.snd c (specMap R k))
    rw [← hinv]
    infer_instance
  haveI : GeometricallyIntegral (baseChange R c k) :=
    AlgebraicGeometry.geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth (baseChange R c k)
      (hH0_baseChange c k hH0)
  haveI : GeometricallyIrreducible (pullback.snd c (specMap R k)) :=
    show GeometricallyIrreducible (baseChange R c k) from inferInstance
  rw [← hhom]
  infer_instance

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

noncomputable def eBA {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (deg : Fin M → ℕ)
    (φ : ∀ i, A ⊗[R] B i ≃ₐ[A] (Fin (deg i) → A)) (Ω : Type u) [Field Ω] [Algebra A Ω] (i : Fin M) :
    (A ⊗[R] B i →ₐ[A] Ω) ≃ Fin (deg i) :=
  Classical.choice (AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
    ((Algebra.TensorProduct.lid A (A ⊗[R] B i)).trans (φ i)) (Algebra.ofId A Ω))

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

end AlgebraicGeometry.RelPicard.HCoverASmooth
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard.HCoverASmooth"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage pullbackSpecIso_inv_snd SmoothOfRelativeDimension IsProper Scheme.Hom GeometricallyIntegral GeometricallyIrreducible isPullback_morphismRestrict Spec Spec.map Scheme Smooth pullbackSpecIso IsOpenImmersion Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Hom.comp_apply geometrically Scheme.Modules.IsInvertible RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom prodKerGraph Scheme.Modules.pullbackTensorUnitObjIso RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension RelPicard.isInvertible_sectionIdeal_of_range_subset RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension isInvertible_sectionIdeal_of_range_subset exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth exists_fibreIso_hom_comp_eq exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth"
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem HCoverA.smooth_branch
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
    (hsm : Smooth (pullback.snd (baseChange R c A) (s ≫ t))) :
    ∃ i : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))),
      ∀ 𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
          (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗
            ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  haveI := HCoverASmooth.smooth_U_baseChange c A U

  have hgoodU_A := HCoverASmooth.range_fst_subset_of_smooth c A U hgoodU (s ≫ t) hsm
  have hgoodirr : GeometricallyIrreducible (pullback.snd (baseChange R c A) (s ≫ t)) := by
    haveI := hsm
    exact HCoverASmooth.geometricallyIrreducible_snd_of_smooth_of_hH0 (baseChange R c A)
      (HCoverASmooth.hH0_baseChange c A hH0) (s ≫ t)

  exact exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth A (baseChange R c A)
    (pullback.fst c (specMap R A) ⁻¹ᵁ U) (sectionBaseChange A ε) (HCoverASmooth.hεU_baseChange c A U ε hεA)
    (HCoverASmooth.hH0_baseChange c A hH0) g e r hr hgr (HCoverASmooth.hg_baseChange c A g hg)
    (fun i => A ⊗[R] B i) (fun i => HCoverASmooth.zA c A (B i) (z i) (hz i))
    (fun i => HCoverASmooth.zA_snd c A (B i) (z i) (hz i))
    (fun i => HCoverASmooth.range_zA_subset c A (B i) (z i) (hz i) U (hzU i))
    (HCoverASmooth.pairwise_disjoint_range_zA c A B z hz hzdisj)
    deg hdeg hdegb hMlt σ hσinj
    (fun i m => by
      obtain ⟨y, hy⟩ := hσfac i m
      exact HCoverASmooth.exists_fac_zA c A (B i) (z i) (hz i) y hy)
    (fun Ω _ _ _ i => HCoverASmooth.eBA A B deg φ Ω i)
    (fun a m => ULift.up (a, m)) Dγ (fun a m => hDγI (ULift.up (a, m)))
    t L hL K s hsm hgoodirr hgoodU_A

end AlgebraicGeometry.RelPicard
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard.HCoverASmooth"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard.HCoverASmooth"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage pullbackSpecIso_inv_snd SmoothOfRelativeDimension IsProper Scheme.Hom GeometricallyIntegral GeometricallyIrreducible isPullback_morphismRestrict Spec Spec.map Scheme Smooth pullbackSpecIso IsOpenImmersion Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Hom.comp_apply geometrically Scheme.Modules.IsInvertible RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom prodKerGraph Scheme.Modules.pullbackTensorUnitObjIso RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension RelPicard.isInvertible_sectionIdeal_of_range_subset RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension isInvertible_sectionIdeal_of_range_subset exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth exists_fibreIso_hom_comp_eq exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth"
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem HCoverA.bad_branch
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
            ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 :=
  AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth c 𝒱 hH0 ε U hεA hgoodU hgred g hg hbad A e r hr B deg hdeg φ z hz hzU hzdisj hzε σ hσfac Dγ hDγI hDγU hσinj hgr b hdegb hMlt
    t L hL K s hns

end AlgebraicGeometry.RelPicard
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard.HCoverASmooth"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard.HCoverASmooth"

open _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.AlgebraicGeometry.RelPicard in
set_option maxHeartbeats 3200000 in

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
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ e + e < M) :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)) (L : RigidifiedLineBundle (baseChange R c A) (sectionBaseChange A ε) t),
      FibrewiseAlgEquivZero L → ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ i : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))), ∀ (𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
          (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by
  classical
  intro T t L hL k _ s

  let K : Type u := AlgebraicClosure k
  let sK : Spec (CommRingCat.of K) ⟶ T := Scheme.TwoAffineOpenCover.specMap k K ≫ s

  obtain ⟨i, hi⟩ : ∃ i : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))),
      ∀ 𝒲 : (pullback (pullback.snd (baseChange R c A) t) sK).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t sK) (fibreModule (baseChange R c A) t sK
          (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗
            ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by
    by_cases hsm : Smooth (pullback.snd (baseChange R c A) (sK ≫ t))
    · exact HCoverA.smooth_branch c 𝒱 hH0 ε U hεA hgoodU hgred g hg hbad A e r hr B deg hdeg φ z hz hzU hzdisj hzε σ hσfac
        Dγ hDγI hDγU hσinj hgr b hdegb hMlt t L hL K sK hsm
    · exact HCoverA.bad_branch c 𝒱 hH0 ε U hεA hgoodU hgred g hg hbad A e r hr B deg hdeg φ z hz hzU hzdisj hzε σ hσfac
        Dγ hDγI hDγU hσinj hgr b hdegb hMlt t L hL K sK hsm
  refine ⟨i, ?_⟩

  haveI : SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) := by
    have hsq : IsPullback ((pullback.fst c (specMap R A)) ∣_ U) (pullback.fst c (specMap R A) ⁻¹ᵁ U).ι U.ι
        (pullback.fst c (specMap R A)) := isPullback_morphismRestrict _ _
    have hbig : IsPullback ((pullback.fst c (specMap R A)) ∣_ U)
        ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) (U.ι ≫ c) (specMap R A) :=
      hsq.paste_vert (IsPullback.of_hasPullback c (specMap R A))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance
  have hεUA : Set.range (sectionBaseChange A ε).1 ⊆ ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) :
      Set ↥(pullback c (specMap R A))) := by
    rintro _ ⟨x, rfl⟩
    show (pullback.fst c (specMap R A)) ((sectionBaseChange A ε).1 x) ∈ U
    rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
    exact hεA ⟨_, rfl⟩
  have hT : Scheme.Modules.IsInvertible (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r) :=
    ((AlgebraicGeometry.RelPicard.isInvertible_sectionIdeal_of_range_subset (baseChange R c A) (sectionBaseChange A ε)
      (pullback.fst c (specMap R A) ⁻¹ᵁ U) hεUA t).pow r).isInvertible_invModule
  have hD : Scheme.Modules.IsInvertible ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule :=
    (AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      ((Dγ i).pullbackAlong t (Category.comp_id t)) ((hDγU i).pullbackAlong t (Category.comp_id t))).isInvertible_module
  have hM := L.isInvertible.tensor (hT.tensor hD)
  exact AlgebraicGeometry.RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension (baseChange R c A) t _ hM s K hi

end S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective (solution)
