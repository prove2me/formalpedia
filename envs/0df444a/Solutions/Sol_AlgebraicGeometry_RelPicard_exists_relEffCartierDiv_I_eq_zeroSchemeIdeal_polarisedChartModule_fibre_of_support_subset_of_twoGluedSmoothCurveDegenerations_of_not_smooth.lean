-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9ebc254b-31c7-503f-aacf-7b700ade4721

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
import Theorems.Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_of_isProper_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth.AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper Scheme.Modules.pullback basicOpen_eq_bot_iff Scheme.Opens.range_ι GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Pullback.range_map GeometricallyIrreducible IsFinite LocallyOfFiniteType GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Scheme Smooth Scheme.Hom.appTop IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_appTop isIntegral_iff_irreducibleSpace_and_isReduced Flat isIso_of_isOpenImmersion_of_opensRange_eq_top IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.preimage_basicOpen_top GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules Scheme.Opens Scheme.Hom.app_eq_appLE IsAffineHom geometrically Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Hom.coe_opensRange isIntegral_of_irreducibleSpace_of_isReduced Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover RelEffCartierDiv.SupportedIn Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible isReduced_of_smooth_over_field RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso sectionFibrePoint fibreModule isAlgEquivZero_iff_eulerChar_sectionsOf_eq finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap"
namespace ZBadE
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

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

theorem isIntegral_of_geometricallyIrreducible_of_isReduced
    {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible q] [IsReduced X] : IsIntegral X := by
  haveI : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := q)
  exact (isIntegral_iff_irreducibleSpace_and_isReduced (X := X)).mpr ⟨inferInstance, inferInstance⟩

theorem finrank_H0_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := by cases 𝒱; cases 𝒱₂; cases h0; cases h1; rfl
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

noncomputable def χ {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    (𝒲 : X.TwoAffineOpenCover) (M : X.Modules) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf q M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf q M).H1

theorem χ_congr {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    (𝒲 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') : χ q 𝒲 M = χ q 𝒲 M' := by
  obtain ⟨h0, h1⟩ := finrank_H0_H1_congr q 𝒲 e
  simp only [χ, h0, h1]

theorem χ_tensor_invModule_tensor_module_eq
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    [IsProper q] [IsIntegral X] [SmoothOfRelativeDimension 1 q]
    (Lx : X.Modules) (hLx : Scheme.Modules.IsInvertible Lx) (h0 : IsAlgEquivZero q Lx)
    (K : X.IdealSheafData) (hK : K.IsInvertible) (ρ : ℕ)
    (hKfin : IsFinite (K.subschemeι ≫ q)) (hKdeg : ∀ t, (K.subschemeι ≫ q).finrank t = ρ)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (e : ℕ)
    (hIfin : IsFinite (I.subschemeι ≫ q)) (hIdeg : ∀ t, (I.subschemeι ≫ q).finrank t = e)
    (g : ℕ) (hr : g + e = ρ) (𝒲 : X.TwoAffineOpenCover) :
    χ q 𝒲 (Lx ⊗ (K.invModule ⊗ I.module)) = χ q 𝒲 (𝟙_ X.Modules) + g := by
  haveI : IsSeparated q := inferInstance

  have hKinv : Scheme.Modules.IsInvertible K.invModule := hK.isInvertible_invModule
  have hImod : Scheme.Modules.IsInvertible I.module := hI.isInvertible_module
  set P : X.Modules := Lx ⊗ (K.invModule ⊗ I.module) with hP
  have hPinv : Scheme.Modules.IsInvertible P := hLx.tensor (hKinv.tensor hImod)

  have ha := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq q hI hIfin hIdeg P hPinv 𝒲

  have eII : I.module ⊗ I.invModule ≅ 𝟙_ X.Modules :=
    @asIso _ _ _ _ ((ihom.ev I.module).app (𝟙_ X.Modules)) (Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hImod)
  have eb : P ⊗ I.invModule ≅ Lx ⊗ K.invModule :=
    (α_ Lx (K.invModule ⊗ I.module) I.invModule) ≪≫
      (Iso.refl Lx ⊗ᵢ ((α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ eII) ≪≫ (ρ_ _)))

  have hc := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq q hK hKfin hKdeg Lx hLx 𝒲

  have hd := (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k q Lx hLx 𝒲).mp h0

  have hb := χ_congr q 𝒲 eb
  simp only [χ] at hb ⊢
  change _ = (Module.finrank k (𝒲.sectionsOf q (𝟙_ X.Modules)).H0 : ℤ) -
    Module.finrank k (𝒲.sectionsOf q (𝟙_ X.Modules)).H1 at hd
  have hr' : (ρ : ℤ) = g + e := by exact_mod_cast hr.symm
  linarith [ha, hb, hc, hd, hr']

noncomputable def coverOfFibre {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover) {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    (pullback c x).TwoAffineOpenCover :=
  haveI : IsAffineHom (pullback.fst c x) := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  { U0 := (pullback.fst c x) ⁻¹ᵁ 𝒱.U0
    U1 := (pullback.fst c x) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

noncomputable def coverPreimage {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i] (𝒲 : X.TwoAffineOpenCover) :
    Y.TwoAffineOpenCover :=
  { U0 := i ⁻¹ᵁ 𝒲.U0
    U1 := i ⁻¹ᵁ 𝒲.U1
    isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage _ }

theorem isIntegral_of_geometricallyIntegral {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [GeometricallyIntegral c] : IsIntegral C :=
  GeometricallyIntegral.geometrically_isIntegral (f := c) (𝟙 _) (𝟙 C) c
    (IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩)

theorem finite_preimage_of_isClosed {k : Type u} [Field k] {X C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [GeometricallyIntegral c] [SmoothOfRelativeDimension 1 c] (i : C ⟶ X)
    (Z : Set ↥X) (hZc : IsClosed Z) (q : C) (hq : i.base q ∉ Z) : (i.base ⁻¹' Z).Finite := by
  haveI := isIntegral_of_geometricallyIntegral c
  let U : C.Opens := ⟨(i.base ⁻¹' Z)ᶜ, (hZc.preimage i.base.hom.continuous).isOpen_compl⟩
  have h := AlgebraicCurve.finite_compl_of_isOpen c U ⟨q, hq⟩
  simpa [U] using h

theorem finite_of_isClosed_of_subset_compl_crossings
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [IsProper c₂] [GeometricallyIntegral c₁] [GeometricallyIntegral c₂]
    [SmoothOfRelativeDimension 1 c₁] [SmoothOfRelativeDimension 1 c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hne : Nonempty ↥(pullback i₁.1 i₂.1))
    (Z : Set ↥X) (hZc : IsClosed Z) (hZ : Z ⊆ (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ) : Z.Finite := by
  obtain ⟨z₀⟩ := hne
  have hmem : (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base z₀ ∉ Z := fun h => hZ h ⟨z₀, rfl⟩
  have h1 : (i₁.1.base ⁻¹' Z).Finite :=
    finite_preimage_of_isClosed c₁ i₁.1 Z hZc ((pullback.fst i₁.1 i₂.1).base z₀) hmem
  have h2 : (i₂.1.base ⁻¹' Z).Finite := by
    refine finite_preimage_of_isClosed c₂ i₂.1 Z hZc ((pullback.snd i₁.1 i₂.1).base z₀) ?_
    have : i₂.1.base ((pullback.snd i₁.1 i₂.1).base z₀) = (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base z₀ := by
      show (pullback.snd i₁.1 i₂.1 ≫ i₂.1).base z₀ = _
      rw [pullback.condition]
    rw [this]
    exact hmem
  refine ((h1.image i₁.1.base).union (h2.image i₂.1.base)).subset ?_
  intro z hz
  rcases hcover z with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl ⟨a, hz, rfl⟩
  · exact Or.inr ⟨b, hz, rfl⟩

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem app_top_algebraMap {k : Type u} [Field k] {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k)) (r : k) :
    (h.app ⊤) ((algebraOfHom g ⊤).algebraMap r) = (algebraOfHom (h ≫ g) (h ⁻¹ᵁ ⊤)).algebraMap r := by
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom, ← CategoryTheory.ConcreteCategory.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem appTop_algebraMap {k : Type u} [Field k] {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
    (g' : Y' ⟶ Spec (CommRingCat.of k)) (e : h ≫ g = g') (r : k) :
    h.appTop ((algebraOfHom g ⊤).algebraMap r) = (algebraOfHom g' ⊤).algebraMap r := by
  subst e
  exact app_top_algebraMap h g r

theorem bijective_algebraMap_of_twoGlued
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsReduced X]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [IsProper c₂] [IsIntegral C₁] [IsIntegral C₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hne : Nonempty ↥(pullback i₁.1 i₂.1)) :
    letI := algebraOfHom x ⊤
    Function.Bijective (algebraMap k Γ(X, ⊤)) := by
  letI := algebraOfHom x ⊤
  letI := algebraOfHom c₁ ⊤
  letI := algebraOfHom c₂ ⊤

  have hb₁ := Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral k c₁
  have hb₂ := Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral k c₂

  have h₁ : ∀ r : k, i₁.1.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(C₁, ⊤) r := fun r =>
    appTop_algebraMap i₁.1 x c₁ i₁.2 r
  have h₂ : ∀ r : k, i₂.1.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(C₂, ⊤) r := fun r =>
    appTop_algebraMap i₂.1 x c₂ i₂.2 r

  obtain ⟨z₀⟩ := hne
  set Z := pullback i₁.1 i₂.1
  letI algZ := algebraOfHom ((pullback.snd i₁.1 i₂.1 ≫ i₂.1) ≫ x) ⊤
  haveI : Nontrivial Γ(Z, ⊤) := (Z.presheaf.germ ⊤ z₀ trivial).hom.domain_nontrivial
  refine ⟨?_, fun f => ?_⟩
  ·
    refine Function.Injective.of_comp (f := (pullback.snd i₁.1 i₂.1 ≫ i₂.1).appTop) ?_
    have : (fun r => (pullback.snd i₁.1 i₂.1 ≫ i₂.1).appTop (algebraMap k Γ(X, ⊤) r)) = algebraMap k Γ(Z, ⊤) := by
      funext r; exact appTop_algebraMap _ x _ rfl r
    rw [Function.comp_def, this]
    exact (algebraMap k Γ(Z, ⊤)).injective
  ·
    obtain ⟨a₁, ha₁⟩ := hb₁.2 (i₁.1.appTop f)
    obtain ⟨a₂, ha₂⟩ := hb₂.2 (i₂.1.appTop f)

    have e₁ : pullback.fst i₁.1 i₂.1 ≫ c₁ = (pullback.snd i₁.1 i₂.1 ≫ i₂.1) ≫ x := by
      rw [Category.assoc, ← pullback.condition_assoc, i₁.2]
    have e₂ : pullback.snd i₁.1 i₂.1 ≫ c₂ = (pullback.snd i₁.1 i₂.1 ≫ i₂.1) ≫ x := by
      rw [Category.assoc, i₂.2]
    have hZ₁ : (pullback.fst i₁.1 i₂.1).appTop (algebraMap k Γ(C₁, ⊤) a₁) = algebraMap k Γ(Z, ⊤) a₁ :=
      appTop_algebraMap _ c₁ _ e₁ a₁
    have hZ₂ : (pullback.snd i₁.1 i₂.1).appTop (algebraMap k Γ(C₂, ⊤) a₂) = algebraMap k Γ(Z, ⊤) a₂ :=
      appTop_algebraMap _ c₂ _ e₂ a₂
    have hf : (pullback.fst i₁.1 i₂.1).appTop (i₁.1.appTop f) = (pullback.snd i₁.1 i₂.1).appTop (i₂.1.appTop f) := by
      have := congrArg (fun φ => Scheme.Hom.appTop φ f) (pullback.condition (f := i₁.1) (g := i₂.1))
      simpa only [Scheme.Hom.comp_appTop, CategoryTheory.ConcreteCategory.comp_apply] using this
    have ha : a₁ = a₂ := by
      apply (algebraMap k Γ(Z, ⊤)).injective
      rw [← hZ₁, ← hZ₂, ha₁, ha₂, hf]
    subst ha
    refine ⟨a₁, ?_⟩

    have hg₁ : i₁.1.appTop (f - algebraMap k Γ(X, ⊤) a₁) = 0 := by rw [map_sub, h₁, ha₁, sub_self]
    have hg₂ : i₂.1.appTop (f - algebraMap k Γ(X, ⊤) a₁) = 0 := by rw [map_sub, h₂, ha₂, sub_self]
    have hbot : X.basicOpen (f - algebraMap k Γ(X, ⊤) a₁) = ⊥ := by
      refine eq_bot_iff.mpr fun z hz => ?_
      rcases hcover z with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hy : y ∈ i₁.1 ⁻¹ᵁ X.basicOpen (f - algebraMap k Γ(X, ⊤) a₁) := hz
        rw [Scheme.preimage_basicOpen_top, hg₁, Scheme.basicOpen_zero] at hy
        exact hy.elim
      · have hy : y ∈ i₂.1 ⁻¹ᵁ X.basicOpen (f - algebraMap k Γ(X, ⊤) a₁) := hz
        rw [Scheme.preimage_basicOpen_top, hg₂, Scheme.basicOpen_zero] at hy
        exact hy.elim
    have := (basicOpen_eq_bot_iff _).mp hbot
    exact (sub_eq_zero.mp this).symm

theorem finrank_H0_unit_eq_one_of_twoGlued
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] [IsAlgClosed k] (xb : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    [IsProper (pullback.snd c xb)] [IsReduced (pullback c xb)]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [IsProper c₂] [GeometricallyIntegral c₁] [GeometricallyIntegral c₂]
    [SmoothOfRelativeDimension 1 c₁] [SmoothOfRelativeDimension 1 c₂]
    (i₁ : SchemeHomOver c₁ (pullback.snd c xb)) (i₂ : SchemeHomOver c₂ (pullback.snd c xb))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback c xb), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hne : Nonempty ↥(pullback i₁.1 i₂.1))
    (𝒲 : (pullback c xb).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (pullback.snd c xb) (SheafOfModules.unit (pullback c xb).ringCatSheaf)).H0 = 1 := by

  haveI : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  haveI : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
  have hH0 := bijective_algebraMap_of_twoGlued k (pullback.snd c xb) c₁ c₂ i₁ i₂ hcover hne

  let φ : pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) xb ≅ pullback c xb :=
    pullbackLeftPullbackSndIso c (𝟙 _) xb ≪≫ pullback.congrHom rfl (Category.comp_id xb)
  have hφ : φ.hom ≫ pullback.snd c xb = fibreAt c (𝟙 _) xb := by
    simp only [φ, fibreAt, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨𝒱', -, -, ⟨h0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) xb) (pullback.snd c xb) φ hφ 𝒲 (SheafOfModules.unit (pullback c xb).ringCatSheaf)
    (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) xb).ringCatSheaf)
    (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  rw [← h0.finrank_eq]
  exact RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap c k xb hH0 𝒱'

end AlgebraicGeometry.RelPicard.ZBadE

open AlgebraicGeometry.RelPicard.ZBadE in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g e ρ : ℕ) (hr : g + e = ρ)
    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγU : Dγ.SupportedIn U)

    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H1 = 1)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgoodirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → GeometricallyIrreducible (pullback.snd c x))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))

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
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1))) :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (_ : ¬ Smooth (pullback.snd c (x ≫ t)))
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U := by
  intro T t _ L hL k _ _ x hns σ hσ hsupp
  classical

  set xb : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := x ≫ t with hxb
  haveI : IsProper (pullback.snd c xb) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : IsReduced (pullback c xb) := hgred k xb

  obtain ⟨C₁, C₂, c₁, c₂, hp₁, hs₁, hgi₁, hp₂, hs₂, hgi₂, i₁, i₂, hci₁, hci₂, n,
    hcover, hred, hn, hn0, hεpt, hUtr, hC1U, hC2U, hW₁, hW₂⟩ := hbad k xb hns
  haveI := hci₁; haveI := hci₂; haveI := hp₁; haveI := hp₂; haveI := hs₁; haveI := hs₂; haveI := hgi₁; haveI := hgi₂

  set ψ : SchemeHomOver xb t := ⟨x, rfl⟩ with hψ
  set Lx := (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj L.L with hLx
  have hLxinv : Scheme.Modules.IsInvertible Lx := L.isInvertible.pullback _
  set Exb : RelEffCartierDiv c ρ xb := E.pullbackAlong xb (Category.comp_id _) with hExb
  set Dxb : RelEffCartierDiv c e xb := Dγ.pullbackAlong xb (Category.comp_id _) with hDxb
  have hETinv : (E.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t (Category.comp_id t))
  have hDTinv : (Dγ.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hDγU.pullbackAlong t (Category.comp_id t))
  have hExbinv : Exb.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong xb (Category.comp_id _))
  have hDxbinv : Dxb.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hDγU.pullbackAlong xb (Category.comp_id _))
  have hcompE : (E.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 = Exb := RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hcompD : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 = Dxb := RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hIE : Exb.I = (E.pullbackAlong t (Category.comp_id t)).I.comap (mapOnProdOver c x rfl) := by rw [← hcompE]; rfl
  have hID : Dxb.I = (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (mapOnProdOver c x rfl) := by rw [← hcompD]; rfl
  obtain ⟨eE'⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (mapOnProdOver c x rfl) hETinv (hIE ▸ hExbinv)
  have eE : (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj (E.pullbackAlong t (Category.comp_id t)).lineBundle ≅ Exb.I.invModule :=
    eE' ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hIE).symm
  have eI : (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅ Dxb.idealModule :=
    @asIso _ _ _ _ ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (mapOnProdOver c x rfl))
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (mapOnProdOver c x rfl) hDTinv (hID ▸ hDxbinv)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hID).symm
  set M' : (pullback c xb).Modules := Exb.I.invModule ⊗ Dxb.idealModule with hM'
  have hM'inv : Scheme.Modules.IsInvertible M' := hExbinv.isInvertible_invModule.tensor hDxbinv.isInvertible_module
  have eN : (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ≅ Lx ⊗ M' :=
    (Scheme.Modules.pullbackTensorObjIso (mapOnProdOver c x rfl) _ _) ≪≫
      (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullbackTensorObjIso (mapOnProdOver c x rfl) _ _) ≪≫ (eE ⊗ᵢ eI)))
  have hNinv : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))) :=
    (L.isInvertible.tensor (hETinv.isInvertible_invModule.tensor hDTinv.isInvertible_module)).pullback _

  have h0 : IsAlgEquivZero (pullback.snd c xb) Lx := by
    set φ := pullbackLeftPullbackSndIso c t x with hφdef
    have he : φ.inv ≫ fibreAt c t x = pullback.snd c xb := by
      rw [hφdef, Iso.inv_comp_eq]
      exact (pullbackLeftPullbackSndIso_hom_snd c t x).symm
    have hfst : φ.inv ≫ pullback.fst (pullback.snd c t) x = mapOnProdOver c x rfl := by
      apply pullback.hom_ext
      · rw [hφdef, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
        simp only [mapOnProdOver, pullback.map, pullback.lift_fst, Category.comp_id]
      · rw [hφdef, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]
        simp only [mapOnProdOver, pullback.map, pullback.lift_snd]
    refine IsAlgEquivZero.of_iso ?_ ((hL k x).pullback φ.inv he)
    exact (Scheme.Modules.pullbackComp φ.inv (pullback.fst (pullback.snd c t) x)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hfst).app _

  let 𝒲 := coverOfFibre c 𝒱 xb

  have hgX : Module.finrank k (𝒲.sectionsOf (pullback.snd c xb)
      (SheafOfModules.unit (pullback c xb).ringCatSheaf)).H1 = g := by
    let φ : pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) xb ≅ pullback c xb :=
      pullbackLeftPullbackSndIso c (𝟙 _) xb ≪≫ pullback.congrHom rfl (Category.comp_id xb)
    have hφ : φ.hom ≫ pullback.snd c xb = fibreAt c (𝟙 _) xb := by
      simp only [φ, fibreAt, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd]
    obtain ⟨𝒱', -, -, -, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c (𝟙 _) xb) (pullback.snd c xb) φ hφ 𝒲 (SheafOfModules.unit (pullback c xb).ringCatSheaf)
      (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) xb).ringCatSheaf)
      (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
    rw [← h1.finrank_eq]
    exact hg k xb 𝒱'

  have hχM' : χ (pullback.snd c xb) 𝒲 M' = 1 := by
    set φ₀ : pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) xb ≅ pullback c xb :=
      pullbackLeftPullbackSndIso c (𝟙 _) xb ≪≫ pullback.congrHom rfl (Category.comp_id xb) with hφ₀def
    have hφ₀ : φ₀.hom ≫ pullback.snd c xb = fibreAt c (𝟙 _) xb := by
      rw [hφ₀def]
      simp only [fibreAt, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd]
    set ψ₀ : SchemeHomOver xb (𝟙 (Spec (CommRingCat.of R))) := ⟨xb, Category.comp_id xb⟩ with hψ₀
    have hfst₀ : φ₀.inv ≫ pullback.fst (pullback.snd c (𝟙 _)) xb = baseChangeSnd c ψ₀ := by
      rw [hφ₀def]
      apply pullback.hom_ext
      · simp only [baseChangeSnd, pullback.map, Iso.trans_inv, Category.assoc, pullback.lift_fst, Category.comp_id,
          pullback.congrHom_inv, pullbackLeftPullbackSndIso_inv_fst]
      · simp only [baseChangeSnd, pullback.map, Iso.trans_inv, Category.assoc, pullback.lift_snd,
          pullback.congrHom_inv, pullback.lift_fst_assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.lift_snd_assoc,
          Category.id_comp]
        rfl
    have hE₀ : Exb.I = E.I.comap (baseChangeSnd c ψ₀) := rfl
    have hI₀ : Dxb.I = Dγ.I.comap (baseChangeSnd c ψ₀) := rfl
    have hEinv : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U _ hEU
    have hDinv : Dγ.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U _ hDγU
    obtain ⟨eE₀⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (baseChangeSnd c ψ₀) hEinv (hE₀ ▸ hExbinv)
    have eI₀ : (Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj Dγ.idealModule ≅ Dxb.idealModule :=
      @asIso _ _ _ _ (Dγ.I.pullbackModuleComparison (baseChangeSnd c ψ₀))
        (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ₀) hDinv (hI₀ ▸ hDxbinv))
    have eF₀ : (Scheme.Modules.pullback φ₀.inv).obj
        (fibreModule c (𝟙 _) xb (E.lineBundle ⊗ Dγ.idealModule)) ≅ M' :=
      ((Scheme.Modules.pullbackComp φ₀.inv (pullback.fst (pullback.snd c (𝟙 _)) xb)).app _) ≪≫
        (Scheme.Modules.pullbackCongr hfst₀).app _ ≪≫
        Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ₀) _ _ ≪≫ (eE₀ ⊗ᵢ eI₀)
    have e' : fibreModule c (𝟙 _) xb (E.lineBundle ⊗ Dγ.idealModule) ≅ (Scheme.Modules.pullback φ₀.hom).obj M' :=
      ((Scheme.Modules.pullbackId _).app _).symm ≪≫
        ((Scheme.Modules.pullbackCongr φ₀.hom_inv_id).app _).symm ≪≫
        ((Scheme.Modules.pullbackComp φ₀.hom φ₀.inv).app _).symm ≪≫
        (Scheme.Modules.pullback φ₀.hom).mapIso eF₀
    obtain ⟨𝒱'', -, -, ⟨h0⟩, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c (𝟙 _) xb) (pullback.snd c xb) φ₀ hφ₀ 𝒲 M' _ e'
    simp only [χ]
    rw [← h0.finrank_eq, ← h1.finrank_eq]
    exact hχ k xb 𝒱''

  have h0X : Module.finrank k (𝒲.sectionsOf (pullback.snd c xb)
      (SheafOfModules.unit (pullback c xb).ringCatSheaf)).H0 = 1 := by
    have hne : Nonempty ↥(pullback i₁.1 i₂.1) := (Nat.card_ne_zero.mp (by rw [hn]; exact hn0.ne')).1
    exact finrank_H0_unit_eq_one_of_twoGlued c k xb c₁ c₂ i₁ i₂ hcover hne 𝒲

  have hZfin : ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c xb)).Finite := by
    have hne : Nonempty ↥(pullback i₁.1 i₂.1) := (Nat.card_ne_zero.mp (by rw [hn]; exact hn0.ne')).1
    refine finite_of_isClosed_of_subset_compl_crossings (pullback.snd c xb) c₁ c₂ i₁ i₂ hcover hne _
      (Scheme.Modules.zeroSchemeIdeal σ).support.isClosed ?_
    rw [← hUtr]
    exact hsupp

  obtain ⟨r, D, hDI⟩ := RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite xb (Scheme.Modules.zeroSchemeIdeal σ) hZfin
  have hDU : D.SupportedIn U := by
    unfold RelEffCartierDiv.SupportedIn
    rw [hDI]; exact hsupp
  have hDinv' : D.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U D hDU
  have hZinv : (Scheme.Modules.zeroSchemeIdeal σ).IsInvertible := hDI ▸ hDinv'
  obtain ⟨eD, -⟩ := Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal hNinv σ hZinv

  have hr1 : χ (pullback.snd c xb) 𝒲 ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))) =
      χ (pullback.snd c xb) 𝒲 (𝟙_ (pullback c xb).Modules) + r := by
    have h := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq (pullback.snd c xb) hDinv'
      D.isFinite D.finrank_eq (𝟙_ (pullback c xb).Modules) (Scheme.Modules.isInvertible_unit _) 𝒲
    have e1 : (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
        𝟙_ (pullback c xb).Modules ⊗ D.I.invModule :=
      eD ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hDI.symm) ≪≫ (λ_ _).symm
    rw [χ_congr (pullback.snd c xb) 𝒲 e1]
    simpa [χ] using h

  have hdeg : χ (pullback.snd c xb) 𝒲 ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))) =
      χ (pullback.snd c xb) 𝒲 M' := by

    have hfinZ : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')

    have hint : ∀ {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of k)) [GeometricallyIntegral c']
        [SmoothOfRelativeDimension 1 c'], IsIntegral C' := by
      intro C' c' _ _
      haveI : GeometricallyIrreducible c' := inferInstance
      haveI : IrreducibleSpace ↥C' := GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := c')
      haveI : IsReduced C' := isReduced_of_smooth_over_field (g := c') (SmoothOfRelativeDimension.smooth 1 c')
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    haveI : IsIntegral C₁ := hint c₁
    haveI : IsIntegral C₂ := hint c₂
    haveI : IsAffineHom i₁.1 := inferInstance
    haveI : IsAffineHom i₂.1 := inferInstance
    let 𝒲₁ := coverPreimage i₁.1 𝒲
    let 𝒲₂ := coverPreimage i₂.1 𝒲
    have hP : Scheme.Modules.IsInvertible (Lx ⊗ M') := hLxinv.tensor hM'inv

    have A1 := AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible k (pullback.snd c xb)
      c₁ c₂ i₁ i₂ hcover hred hfinZ n hn (Lx ⊗ M') hP 𝒲 𝒲₁ 𝒲₂
    have A2 := AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible k (pullback.snd c xb)
      c₁ c₂ i₁ i₂ hcover hred hfinZ n hn M' hM'inv 𝒲 𝒲₁ 𝒲₂

    have comp : ∀ {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of k)) [IsProper c'] [IsIntegral C']
        [SmoothOfRelativeDimension 1 c'] (i' : SchemeHomOver c' (pullback.snd c xb)) (𝒲' : C'.TwoAffineOpenCover),
        χ c' 𝒲' ((Scheme.Modules.pullback i'.1).obj (Lx ⊗ M')) = χ c' 𝒲' ((Scheme.Modules.pullback i'.1).obj M') := by
      intro C' c' _ _ _ i' 𝒲'
      have hL' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i'.1).obj Lx) := hLxinv.pullback _
      have hM'' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i'.1).obj M') := hM'inv.pullback _
      have h0' : IsAlgEquivZero c' ((Scheme.Modules.pullback i'.1).obj Lx) := h0.pullback i'.1 i'.2
      have e := Scheme.Modules.pullbackTensorObjIso i'.1 Lx M'
      have hten := Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub k c' _ _ hL' hM'' 𝒲'
      have halg := (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k c' _ hL' 𝒲').mp h0'
      rw [χ_congr c' 𝒲' e]
      simp only [χ] at hten halg ⊢
      rw [hten, halg]
      ring
    have c1 := comp c₁ i₁ 𝒲₁
    have c2 := comp c₂ i₂ 𝒲₂
    rw [χ_congr (pullback.snd c xb) 𝒲 eN]
    simp only [χ] at A1 A2 c1 c2 ⊢
    rw [A1, A2, c1, c2]

  have hunit : (Module.finrank k (𝒲.sectionsOf (pullback.snd c xb) (𝟙_ (pullback c xb).Modules)).H0 : ℤ) = 1 ∧
      (Module.finrank k (𝒲.sectionsOf (pullback.snd c xb) (𝟙_ (pullback c xb).Modules)).H1 : ℤ) = g := by
    exact ⟨by exact_mod_cast h0X, by exact_mod_cast hgX⟩
  have hrg : r = g := by
    have h1 := hr1.symm.trans (hdeg.trans hχM')
    simp only [χ, hunit.1, hunit.2] at h1
    omega
  subst hrg
  exact ⟨D, hDI, hDU⟩

end S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth (solution)
