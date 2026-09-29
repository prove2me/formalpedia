-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5d779936-5ebc-5e94-856f-473ded0c9ee3

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4"
p2m_attr_erase "simp" "ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicCurve~genus"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap prodKerGraph graphOver graphOver_snd Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint HasChartSections nonempty_pullback_sectionTwist_iso exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed"
namespace K7cov35
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R]

section Probe
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  [GeometricallyIntegral c] {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
example : IsProper (pullback.snd c x) := inferInstance
example : IsSeparated (pullback.snd c x) := inferInstance
example : SmoothOfRelativeDimension 1 (pullback.snd c x) := inferInstance
example : GeometricallyIntegral (pullback.snd c x) := inferInstance
example : IsIntegral (pullback c x) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c x)
example : IsLocalRing k := inferInstance
example : (𝟙_ (pullback c x).Modules)
    = (SheafOfModules.unit (pullback c x).ringCatSheaf : (pullback c x).Modules) := rfl
example : fibreAt c (𝟙 _) x = pullback.snd (pullback.snd c (𝟙 _)) x := rfl
example (X : Scheme.{u}) (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U := rfl
end Probe

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem nonempty_linearEquiv_of_iso {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem eulerChar_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e
  rw [e0.finrank_eq, e1.finrank_eq]

theorem finrank_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨-, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e
  exact e1.finrank_eq

def isoPullbackInvOfIso {X Y : Scheme.{u}} (φ : X ≅ Y) {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj N) : N ≅ (Scheme.Modules.pullback φ.inv).obj M :=
  ((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e.symm

section FibreIso

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (hx : s ≫ t = x)

def fibreIso : pullback (pullback.snd c t) s ≅ pullback c x :=
  pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c t s x hx).hom ≫ pullback.snd c x = fibreAt c t s := by
  subst hx
  simp [fibreIso, fibreAt, pullback.congrHom_hom]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c t s x hx).hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t := by
  subst hx
  simp [fibreIso, pullback.congrHom_hom]

theorem fibreIso_inv_fibreAt : (fibreIso c t s x hx).inv ≫ fibreAt c t s = pullback.snd c x := by
  rw [← fibreIso_hom_snd c t s x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c t s x hx).hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)
      = pullback.fst (pullback.snd c t) s := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    rfl

def fibreModuleIso (F : (pullback c t).Modules) :
    fibreModule c t s F ≅ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj F) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c t s x hx).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c t s x hx).hom
      (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).app F).symm

def fibreUnitIso :
    (𝟙_ (pullback (pullback.snd c t) s).Modules) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj (𝟙_ (pullback c x).Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso (fibreIso c t s x hx).hom).symm

variable [IsSeparated c] [SmoothOfRelativeDimension 1 c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem nonempty_chartModule_iso (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) :
    Nonempty (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
        (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)) := by
  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso R c ε (⟨s, hx⟩ : SchemeHomOver x t) r
  have hI : D.I.IsInvertible := D.isInvertible_I
  have hI' : (D.I.comap (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).IsInvertible :=
    (D.pullbackAlong s hx).isInvertible_I
  let eI : (Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj D.idealModule ≅
      (D.pullbackAlong s hx).idealModule :=
    @asIso _ _ _ _ (D.I.pullbackModuleComparison (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)))
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
        (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)) hI hI')
  exact ⟨fibreModuleIso c t s x hx _ ≪≫ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).mapIso
    (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eT ⊗ᵢ eI))⟩

theorem exists_cover_chart_of_cover (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t)
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H1) := by
  obtain ⟨eM⟩ := nonempty_chartModule_iso c t s x hx ε r D
  obtain ⟨𝒲, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (pullback.snd c x) (fibreIso c t s x hx) (fibreIso_hom_snd c t s x hx) 𝒱 _ _ eM
  exact ⟨𝒲, h0, h1⟩

theorem exists_cover_of_cover_chart (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H1) := by
  obtain ⟨eM⟩ := nonempty_chartModule_iso c t s x hx ε r D
  obtain ⟨𝒱, -, -, ⟨h0⟩, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c x) (fibreAt c t s) (fibreIso c t s x hx).symm (fibreIso_inv_fibreAt c t s x hx) 𝒲 _ _
    (isoPullbackInvOfIso (fibreIso c t s x hx) eM)
  exact ⟨𝒱, ⟨h0.symm⟩, ⟨h1.symm⟩⟩

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
include hx in

theorem exists_cover_of_cover_unit (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H0
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H1
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 := by
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c x) (fibreAt c t s) (fibreIso c t s x hx).symm (fibreIso_inv_fibreAt c t s x hx) 𝒲 _ _
    (isoPullbackInvOfIso (fibreIso c t s x hx) (fibreUnitIso c t s x hx))
  exact ⟨𝒱, e0.finrank_eq.symm, e1.finrank_eq.symm⟩

end FibreIso

end AlgebraicGeometry.RelPicard.K7cov35

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap prodKerGraph graphOver graphOver_snd Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint HasChartSections nonempty_pullback_sectionTwist_iso exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed"
namespace K7cov35
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

theorem exists_section_ne_zero {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (h : Nontrivial (𝒱.sectionsOf x M).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱.sectionsOf x M).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  exact exists_hom_ne_zero M (eΓ.symm y) hσ

end AlgebraicGeometry.RelPicard.K7cov35

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap prodKerGraph graphOver graphOver_snd Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint HasChartSections nonempty_pullback_sectionTwist_iso exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed"
namespace K7cov35
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem geom
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (n g r : ℕ) (hgr : 2 * g < r)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    (hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  haveI : IsSeparated c := inferInstance
  haveI : IsIntegral (pullback c (s ≫ t)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c (s ≫ t))
  haveI : IsProper (pullback.snd c (s ≫ t)) := inferInstance
  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := fibreIso c t s (s ≫ t) rfl

  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top (pullback.snd c (s ≫ t))
    (fun F => AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset (pullback.snd c (s ≫ t)) F)
  let 𝒱 : (pullback c (s ≫ t)).TwoAffineOpenCover := ⟨U, V, hU, hV, hsup, hUV⟩

  let LY : (pullback c (s ≫ t)).Modules :=
    (Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj L.L
  let TwY : (pullback c (s ≫ t)).Modules := sectionTwist c ε (s ≫ t) r
  have hσ : rigSection c (s ≫ t) ε ≫ pullback.snd c (s ≫ t) = 𝟙 _ := pullback.lift_snd _ _ _
  have hLY : Scheme.Modules.IsInvertible LY := L.isInvertible.pullback _
  have hTwY : Scheme.Modules.IsInvertible TwY :=
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (s ≫ t) ε) hσ).pow r).isInvertible_invModule
  have hLT : Scheme.Modules.IsInvertible (LY ⊗ TwY) := hLY.tensor hTwY

  have hAEZ : IsAlgEquivZero (pullback.snd c (s ≫ t)) LY :=
    (((hL K s).pullback φ.inv (fibreIso_inv_fibreAt c t s (s ≫ t) rfl)).of_iso
      (isoPullbackInvOfIso φ (fibreModuleIso c t s (s ≫ t) rfl L.L)).symm)

  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso R c ε (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) r
  let eLT : fibreModule c t s (L.L ⊗ sectionTwist c ε t r) ≅ (Scheme.Modules.pullback φ.hom).obj (LY ⊗ TwY) :=
    Scheme.Modules.pullbackTensorObjIso (pullback.fst (pullback.snd c t) s) L.L (sectionTwist c ε t r) ≪≫
      (fibreModuleIso c t s (s ≫ t) rfl L.L ⊗ᵢ
        (fibreModuleIso c t s (s ≫ t) rfl (sectionTwist c ε t r) ≪≫ (Scheme.Modules.pullback φ.hom).mapIso eT)) ≪≫
      (Scheme.Modules.pullbackTensorObjIso φ.hom LY TwY).symm

  have hr1 : 2 * g ≤ r + 1 := by omega
  have hcut := subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
    R c ε g hg L hL r hr1 K s
  obtain ⟨𝒲₁, -, -, ⟨f0⟩, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (pullback.snd c (s ≫ t)) φ (fibreIso_hom_snd c t s (s ≫ t) rfl) 𝒱 (LY ⊗ TwY)
    (fibreModule c t s (L.L ⊗ sectionTwist c ε t r)) eLT
  obtain ⟨hs1, hf0⟩ := hcut 𝒲₁
  have h0Y : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 = r + 1 - g :=
    f0.finrank_eq.symm.trans hf0
  have h1Y : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1 = 0 := by
    haveI : Subsingleton (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1 :=
      Equiv.subsingleton f1.symm.toEquiv
    exact Module.finrank_zero_of_subsingleton

  obtain ⟨hH1u, hH0u⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K
    (pullback.snd c (s ≫ t)) g (hg K (s ≫ t)) 𝒱
  have hH1u' : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H1 = g :=
    hH1u
  have hH0u' : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H0 = 1 :=
    hH0u

  have hpos : 0 < Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 := by
    rw [h0Y]; omega
  have hnt : Nontrivial (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨sec, hsec⟩ := exists_section_ne_zero (pullback.snd c (s ≫ t)) 𝒱 (LY ⊗ TwY) hnt
  have hχLT : (Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 : ℤ)
        - Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1
      = (Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H0 : ℤ)
        - Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H1 + r := by
    rw [h0Y, h1Y, hH1u', hH0u']
    omega
  obtain ⟨D, -, ⟨eD, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := c)
    (s ≫ t) hLT sec hsec 𝒱 r hχLT
  obtain ⟨Pt, hPt, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D

  obtain ⟨F, instF, instA, M, e, he, -, hch⟩ := hγ K (s ≫ t)
  haveI : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hpt : ∀ m : Fin r, (graphOver c (Pt m) (hPt m) ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun m => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact graphOver_snd c (Pt m) (hPt m)
  have heff : ∀ v : Place K F, 0 ≤ (∑ m : Fin r, Finsupp.single (M.pointEquivPlace ⟨graphOver c (Pt m) (hPt m) ≫ e.inv, hpt m⟩) (1 : ℤ)) v := by
    classical
    intro v
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun m _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hdeg : Divisor.degree (∑ m : Fin r, Finsupp.single (M.pointEquivPlace ⟨graphOver c (Pt m) (hPt m) ≫ e.inv, hpt m⟩) (1 : ℤ)) = r := by
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨i, hi⟩ := hch _ heff hdeg

  refine ⟨i, fun 𝒲 => ?_⟩

  have hχi := hχ i
  generalize hEt : (Dγ i).pullbackAlong t (Category.comp_id t) = Et at ⊢
  let Ei : RelEffCartierDiv c (r - g) (s ≫ t) := Et.pullbackAlong s rfl
  have hγx : ∀ j : Fin (r - g), ((s ≫ t) ≫ (γ i j).1) ≫ c = s ≫ t := fun j => by
    rw [Category.assoc, (γ i j).2, Category.comp_id]
  have hEiI : Ei.I = prodKerGraph c (fun j => (s ≫ t) ≫ (γ i j).1) hγx := by
    have h1 : Ei = (Dγ i).pullbackAlong (s ≫ t) (Category.comp_id _) := by
      show Et.pullbackAlong s rfl = _
      rw [← hEt, RelEffCartierDiv.pullbackAlong_comp]
    rw [h1]
    show (Dγ i).I.comap (mapOnProdOver c (s ≫ t) (Category.comp_id _)) = _
    rw [hDγ i]
    exact prodKerGraph_comap_mapOnProdOver (f := c) (fun j => (γ i j).1) (fun j => (γ i j).2) (s ≫ t)
      (Category.comp_id _)
  have hEi : Scheme.Modules.IsInvertible Ei.idealModule := Ei.isInvertible_I.isInvertible_module
  let Nc : (pullback c (s ≫ t)).Modules := TwY ⊗ Ei.idealModule
  have hNc : Scheme.Modules.IsInvertible Nc := hTwY.tensor hEi

  obtain ⟨eCh⟩ := nonempty_chartModule_iso c t s (s ≫ t) rfl ε r Et
  let eF : fibreModule c t s (L.L ⊗ (sectionTwist c ε t r ⊗ Et.idealModule)) ≅
      (Scheme.Modules.pullback φ.hom).obj (LY ⊗ Nc) :=
    Scheme.Modules.pullbackTensorObjIso (pullback.fst (pullback.snd c t) s) L.L (sectionTwist c ε t r ⊗ Et.idealModule) ≪≫
      (fibreModuleIso c t s (s ≫ t) rfl L.L ⊗ᵢ eCh) ≪≫
      (Scheme.Modules.pullbackTensorObjIso φ.hom LY Nc).symm
  obtain ⟨𝒱', -, -, ⟨g0⟩, ⟨g1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c (s ≫ t)) (fibreAt c t s) φ.symm (fibreIso_inv_fibreAt c t s (s ≫ t) rfl) 𝒲 _ _
    (isoPullbackInvOfIso φ eF)

  suffices hY : Subsingleton (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 by
    exact Equiv.subsingleton g1.symm.toEquiv

  have hcast : D.lineBundle ⊗ Ei.idealModule =
      (∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module := by
    show D.I.invModule ⊗ Ei.I.module = _
    rw [hDI, hEiI]
    rfl
  let eMN := (α_ LY TwY Ei.idealModule).symm ≪≫ whiskerRightIso eD Ei.idealModule ≪≫ eqToIso hcast
  have hd : Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H0 ∧
      Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H1 ∧
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H0 = 1 := by
    obtain ⟨fin0, fin1, hrk⟩ :=
      AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
        (pullback.snd c (s ≫ t)) M e he
        (fun m : Fin r => (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}))
        (fun j : Fin (r - g) => sectionFibrePoint (γ i j) (s ≫ t)) 𝒱'
    exact ⟨fin0, fin1, hrk.trans hi⟩
  obtain ⟨fin0, fin1, hrk⟩ := hd
  obtain ⟨⟨k0⟩, ⟨k1⟩⟩ := nonempty_linearEquiv_of_iso (pullback.snd c (s ≫ t)) 𝒱' eMN
  have hM0 : Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H0 = 1 :=
    k0.finrank_eq.trans hrk
  haveI hM1fin : Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 :=
    Module.Finite.equiv k1.symm

  have hχc := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq (pullback.snd c (s ≫ t)) 𝒱' LY Nc hLY hNc hAEZ
  have hχ' : (Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) Nc).H0 : ℤ) -
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) Nc).H1 = 1 := by
    show (Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t))
        (sectionTwist c ε (s ≫ t) r ⊗ (Et.pullbackAlong s rfl).idealModule)).H0 : ℤ) -
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t))
        (sectionTwist c ε (s ≫ t) r ⊗ (Et.pullbackAlong s rfl).idealModule)).H1 = 1
    rw [← hEt, RelEffCartierDiv.pullbackAlong_comp]
    obtain ⟨𝒲₀, ⟨w0⟩, ⟨w1⟩⟩ :=
      exists_cover_chart_of_cover c (𝟙 _) (s ≫ t) (s ≫ t) (Category.comp_id _) ε r (Dγ i) 𝒱'
    rw [← w0.finrank_eq, ← w1.finrank_eq]
    exact hχi K (s ≫ t) 𝒲₀
  have hM1 : Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 = 0 := by omega
  exact Module.finrank_zero_iff.mp hM1

end AlgebraicGeometry.RelPicard.K7cov35

open AlgebraicGeometry.RelPicard.K7cov35 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (n g r : ℕ) (hgr : 2 * g < r)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    (hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  obtain ⟨i, hi⟩ := geom R c ε n g r hgr hg γ hγ Dγ hDγ hχ t L hL (AlgebraicClosure k)
    (Scheme.TwoAffineOpenCover.specMap k (AlgebraicClosure k) ≫ s)
  refine ⟨i, fun 𝒲 => ?_⟩
  haveI : IsSeparated c := inferInstance
  have hσ : rigSection c t ε ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  have hTw : Scheme.Modules.IsInvertible (sectionTwist c ε t r) :=
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t ε) hσ).pow r).isInvertible_invModule
  have hF : Scheme.Modules.IsInvertible
      (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) :=
    L.isInvertible.tensor (hTw.tensor ((Dγ i).pullbackAlong t (Category.comp_id t)).isInvertible_I.isInvertible_module)
  obtain ⟨𝒲', -, hH1⟩ :=
    exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff c t
      (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) hF s 𝒲
      (AlgebraicClosure k)
  exact hH1.mp (hi 𝒲')

end

end S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre (solution)
