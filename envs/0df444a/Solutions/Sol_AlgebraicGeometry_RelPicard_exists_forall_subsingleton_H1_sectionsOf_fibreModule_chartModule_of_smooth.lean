-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4659fcc2-80b5-50e1-bdbe-4c3786fb0105

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
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_eulerChar_sectionsOf_invModule_pow_ker_tensor_module_prod_ker_eq
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add RegularLocalRingQuotientAscent.dualNumberFst_apply"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra"

noncomputable section

namespace FltWs11
namespace HCSM

theorem isAlgEquivZero_pullbackAlong_L_of_fibrewiseAlgEquivZero
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] (ψ : SchemeHomOver (specMap R Ω) t) :
    IsAlgEquivZero (pullback.snd c (specMap R Ω)) (M.pullbackAlong ψ).L := by

  have h1 := (hM.pullback ψ) Ω (𝟙 (Spec (CommRingCat.of Ω)))

  set f₁ := pullback.fst (pullback.snd c (specMap R Ω)) (𝟙 (Spec (CommRingCat.of Ω))) with hf₁
  haveI : IsIso f₁ := by rw [hf₁]; infer_instance
  have he : inv f₁ ≫ fibreAt c (specMap R Ω) (𝟙 _) = pullback.snd c (specMap R Ω) := by
    rw [IsIso.inv_comp_eq]
    show pullback.snd (pullback.snd c (specMap R Ω)) (𝟙 _) = f₁ ≫ pullback.snd c (specMap R Ω)
    rw [hf₁, pullback.condition, Category.comp_id]
  refine IsAlgEquivZero.of_iso ?_ (h1.pullback (inv f₁) he)

  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f₁)).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

p2m_open "CategoryTheory.MonoidalCategory"

def isoPullbackInvOfIso {X Y : Scheme.{u}} (φ : X ≅ Y) {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj N) : N ≅ (Scheme.Modules.pullback φ.inv).obj M :=
  ((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e.symm

section FibreIso

variable {R' : Type u} [CommRing R'] {C'' : Scheme.{u}} (c'' : C'' ⟶ Spec (CommRingCat.of R'))
  {P : Scheme.{u}} (t₀ : P ⟶ Spec (CommRingCat.of R'))
  {Ω : Type u} [Field Ω] (y : Spec (CommRingCat.of Ω) ⟶ P) (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R'))
  (hx : y ≫ t₀ = x)

def fibreIso : pullback (pullback.snd c'' t₀) y ≅ pullback c'' x :=
  pullbackLeftPullbackSndIso c'' t₀ y ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c'' t₀ y x hx).hom ≫ pullback.snd c'' x = fibreAt c'' t₀ y := by
  subst hx
  simp [fibreIso, fibreAt, pullback.congrHom_hom]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c'' t₀ y x hx).hom ≫ pullback.fst c'' x = pullback.fst (pullback.snd c'' t₀) y ≫ pullback.fst c'' t₀ := by
  subst hx
  simp [fibreIso, pullback.congrHom_hom]

theorem fibreIso_inv_fibreAt : (fibreIso c'' t₀ y x hx).inv ≫ fibreAt c'' t₀ y = pullback.snd c'' x := by
  rw [← fibreIso_hom_snd c'' t₀ y x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c'' t₀ y x hx).hom ≫ baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀)
      = pullback.fst (pullback.snd c'' t₀) y := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    try rfl

def fibreModuleIso (M : (pullback c'' t₀).Modules) :
    fibreModule c'' t₀ y M ≅ (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj M) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c'' t₀ y x hx).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c'' t₀ y x hx).hom
      (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).app M).symm

def fibreUnitIso :
    (𝟙_ (pullback (pullback.snd c'' t₀) y).Modules) ≅
      (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj (𝟙_ (pullback c'' x).Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso (fibreIso c'' t₀ y x hx).hom).symm

def fibreModuleTensorIso (M N : (pullback c'' t₀).Modules) :
    fibreModule c'' t₀ y (M ⊗ N) ≅ (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj
      (((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj M) ⊗
        ((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj N)) :=
  fibreModuleIso c'' t₀ y x hx (M ⊗ N) ≪≫
    (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).mapIso (Scheme.Modules.pullbackTensorObjIso _ M N)

theorem forall_subsingleton_H1_fibre_of_iso {Z : Scheme.{u}} (Φ : pullback (pullback.snd c'' t₀) y ≅ Z)
    (z : Z ⟶ Spec (CommRingCat.of Ω)) (hΦ : Φ.hom ≫ z = fibreAt c'' t₀ y)
    (F : (pullback c'' t₀).Modules) (F' : Z.Modules)
    (eF : fibreModule c'' t₀ y F ≅ (Scheme.Modules.pullback Φ.hom).obj F')
    (h : ∀ 𝒱 : Z.TwoAffineOpenCover, Subsingleton (𝒱.sectionsOf z F').H1)
    (𝒲 : (pullback (pullback.snd c'' t₀) y).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c'' t₀ y) (fibreModule c'' t₀ y F)).H1 := by
  have hΦ' : Φ.inv ≫ fibreAt c'' t₀ y = z := by rw [← hΦ, Iso.inv_hom_id_assoc]
  obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    z (fibreAt c'' t₀ y) Φ.symm hΦ' 𝒲 _ _ (isoPullbackInvOfIso Φ eF)
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

end FibreIso

section Fibre

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

theorem smoothOfRelativeDimension_snd_of_range_subset (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {Y : Scheme.{u}} (x : Y ⟶ Spec (CommRingCat.of R))
    (hU : Set.range (pullback.fst c x).base ⊆ (U : Set C)) :
    SmoothOfRelativeDimension 1 (pullback.snd c x) := by
  have hsurj : Function.Surjective (pullback.snd U.ι (pullback.fst c x)).base := by
    intro y
    have hy : (pullback.fst c x).base y ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hU ⟨y, rfl⟩
    obtain ⟨u, hu⟩ := hy
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback u y hu
    exact ⟨w, hw2⟩
  haveI : Epi (pullback.snd U.ι (pullback.fst c x)).base := (TopCat.epi_iff_surjective _).mpr hsurj
  haveI : IsIso (pullback.snd U.ι (pullback.fst c x)) := IsOpenImmersion.isIso _
  have h1 : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) x) := inferInstance
  have heq : (pullbackRightPullbackFstIso c x U.ι).inv ≫ pullback.snd U.ι (pullback.fst c x) ≫ pullback.snd c x =
      pullback.snd (U.ι ≫ c) x :=
    pullbackRightPullbackFstIso_inv_snd_snd _ _ _
  rw [← heq] at h1
  have h2 := (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
    (pullbackRightPullbackFstIso c x U.ι).inv _).mp h1
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
    (pullback.snd U.ι (pullback.fst c x)) _).mp h2

variable (k : Type u) [Field k] [Algebra R k]

theorem isIntegral_pullback_of_smooth_of_geometricallyIrreducible [IsAlgClosed k]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hsm : Smooth (pullback.snd c (specMap R k))) (hgi : GeometricallyIrreducible (pullback.snd c (specMap R k))) :
    IsIntegral (pullback c (specMap R k)) :=
  haveI := hgi
  isIntegral_of_smooth_of_geometricallyConnected k (pullback.snd c (specMap R k)) hsm
    (GeometricallyIrreducible.geometricallyConnected _) (sectionFibrePoint ε (specMap R k)).1
    (sectionFibrePoint ε (specMap R k)).2

theorem finrank_H1_unit_eq_of_forall_fibre (g : ℕ)
    (hg : ∀ (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) (specMap R k)).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) (specMap R k))
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) (specMap R k)).ringCatSheaf)).H1 = g)
    (𝒱 : (pullback c (specMap R k)).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c (specMap R k)) (𝟙_ (pullback c (specMap R k)).Modules)).H1 = g := by
  obtain ⟨𝒲, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) (specMap R k)) (pullback.snd c (specMap R k))
    (fibreIso c (𝟙 _) (specMap R k) (specMap R k) (Category.comp_id _))
    (fibreIso_hom_snd c (𝟙 _) (specMap R k) (specMap R k) (Category.comp_id _)) 𝒱 (𝟙_ _) (𝟙_ _)
    (fibreUnitIso c (𝟙 _) (specMap R k) (specMap R k) (Category.comp_id _))
  rw [← hg 𝒲]
  exact e1.finrank_eq.symm

theorem nonempty_twoAffineOpenCover_of_fibre {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (s : Spec (CommRingCat.of k) ⟶ T) (hx : s ≫ t = specMap R k)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Nonempty ((pullback c (specMap R k)).TwoAffineOpenCover) := by
  obtain ⟨𝒱, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c (specMap R k)) (fibreAt c t s) (fibreIso c t s (specMap R k) hx).symm
    (fibreIso_inv_fibreAt c t s (specMap R k) hx) 𝒲 (𝟙_ _) (𝟙_ _)
    (Scheme.Modules.pullbackTensorUnitObjIso _).symm
  exact ⟨𝒱⟩

theorem exists_algHom_graphOver_fst_eq {Bi : Type u} [CommRing Bi] [Algebra R Bi]
    (z : Spec (CommRingCat.of Bi) ⟶ C) (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Bi)))
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hσ : ∃ y : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of Bi), σ.1 = y ≫ z) :
    ∃ ψ : Bi →ₐ[R] k,
      graphOver c (specMap R k ≫ σ.1) (by rw [Category.assoc, σ.2, Category.comp_id]) ≫
          pullback.fst c (specMap R k) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z := by
  obtain ⟨y, hy⟩ := hσ
  let ψ₀ : Bi →+* k := (Spec.preimage (specMap R k ≫ y)).hom
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀) = specMap R k ≫ y := by
    simp only [ψ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomp : ψ₀.comp (algebraMap R Bi) = algebraMap R k := by
    have h1 : Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap R Bi))) =
        Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ₀, ← hz, Category.assoc, ← Category.assoc y, ← hy, σ.2,
        Category.comp_id]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hcomm : ∀ a : R, ψ₀.toFun (algebraMap R Bi a) = algebraMap R k a := fun a => by
    have := congrArg (fun h : R →+* k => h a) hcomp
    simpa using this
  refine ⟨AlgHom.mk ψ₀ hcomm, ?_⟩
  show _ = Spec.map (CommRingCat.ofHom ψ₀) ≫ z
  rw [hψ₀, graphOver_fst, hy, Category.assoc]

theorem isInvertible_I_pullbackAlong_of_prodKerGraph [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {n : ℕ} (σs : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hσU : ∀ j, Set.range (σs j).1.base ⊆ (U : Set C))
    (E : RelEffCartierDiv c n (𝟙 (Spec (CommRingCat.of R))))
    (hE : E.I = prodKerGraph c (fun j => (σs j).1) (fun j => (σs j).2))
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (E.pullbackAlong u (Category.comp_id u)).I.IsInvertible := by
  obtain ⟨D, hD, hDU⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn (f := c) U
    (fun j => (σs j).1) (fun j => (σs j).2) hσU
  have hEU : E.SupportedIn U := by
    unfold RelEffCartierDiv.SupportedIn at hDU ⊢
    rw [hE, ← hD]
    exact hDU
  exact RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong u (Category.comp_id u))

end Fibre

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S} in
theorem graphOver_congr {a a' : T ⟶ 𝒞} (h : a = a') (ha : a ≫ f = g) (ha' : a' ≫ f = g) :
    graphOver f a ha = graphOver f a' ha' := by
  subst h
  rfl

theorem slice4_nonempty_pullback_twist_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] [Algebra R k]
    (s : Spec (CommRingCat.of k) ⟶ T) (hsk : s ≫ t = specMap R k)
    (L : (pullback c t).Modules) (r : ℕ) {n : ℕ}
    (σs : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (E : RelEffCartierDiv c n (𝟙 (Spec (CommRingCat.of R))))
    (hE : E.I = prodKerGraph c (fun j => (σs j).1) (fun j => (σs j).2))
    (hTt : ((sectionIdeal c ε t) ^ r).IsInvertible)
    (hTx : ((sectionIdeal c ε (specMap R k)) ^ r).IsInvertible)
    (hDt : (E.pullbackAlong t (Category.comp_id t)).I.IsInvertible)
    (hDx : (E.pullbackAlong (specMap R k) (Category.comp_id _)).I.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hsk⟩ : SchemeHomOver (specMap R k) t))).obj
        (L ⊗ (sectionTwist c ε t r ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
      (Scheme.Modules.pullback (baseChangeSnd c (⟨s, hsk⟩ : SchemeHomOver (specMap R k) t))).obj L ⊗
        ((((sectionFibrePoint ε (specMap R k)).1.ker) ^ r).invModule ⊗
          (∏ j, (graphOver c (specMap R k ≫ (σs j).1)
            (by rw [Category.assoc, (σs j).2, Category.comp_id])).ker).module)) := by
  classical
  set b := baseChangeSnd c (⟨s, hsk⟩ : SchemeHomOver (specMap R k) t) with hbdef

  have hb : b = mapOnProdOver c s hsk := rfl

  have hEx : ((E.pullbackAlong t (Category.comp_id t)).I).comap b =
      ∏ j, (graphOver c (specMap R k ≫ (σs j).1) (by rw [Category.assoc, (σs j).2, Category.comp_id])).ker := by
    have h1 : ((E.pullbackAlong t (Category.comp_id t)).pullbackAlong s hsk).I =
        (E.pullbackAlong (s ≫ t) (by rw [Category.assoc, Category.comp_id, hsk])).I :=
      congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_comp E t (Category.comp_id t) s hsk)
    change ((E.pullbackAlong t (Category.comp_id t)).pullbackAlong s hsk).I = _
    rw [h1]
    change E.I.comap (mapOnProdOver c (s ≫ t) _) = _
    rw [hE, prodKerGraph_comap_mapOnProdOver, prodKerGraph_eq_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [graphOver_congr c (show (s ≫ t) ≫ (σs j).1 = specMap R k ≫ (σs j).1 by rw [hsk])]

  have hEx' : (E.pullbackAlong (specMap R k) (Category.comp_id _)).I =
      ∏ j, (graphOver c (specMap R k ≫ (σs j).1) (by rw [Category.assoc, (σs j).2, Category.comp_id])).ker := by
    change E.I.comap (mapOnProdOver c (specMap R k) _) = _
    rw [hE, prodKerGraph_comap_mapOnProdOver, prodKerGraph_eq_prod]

  have hS1 : ∀ (u : T ⟶ Spec (CommRingCat.of R)), sectionIdeal c ε u =
      prodKerGraph c (fun _ : Fin 1 => u ≫ ε.1) (fun _ => by rw [Category.assoc, ε.2, Category.comp_id]) := by
    intro u
    rw [prodKerGraph_one]
    rfl
  have hpow : ∀ (u : T ⟶ Spec (CommRingCat.of R)), (sectionIdeal c ε u) ^ r =
      prodKerGraph c (fun _ : Fin r => u ≫ ε.1) (fun _ => by rw [Category.assoc, ε.2, Category.comp_id]) := by
    intro u
    rw [prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hTcomap : ((sectionIdeal c ε t) ^ r).comap b = (sectionFibrePoint ε (specMap R k)).1.ker ^ r := by
    rw [hpow t, hb, prodKerGraph_comap_mapOnProdOver, prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    rw [graphOver_congr c (show s ≫ t ≫ ε.1 = specMap R k ≫ ε.1 by rw [← Category.assoc, hsk]) _
      (by rw [Category.assoc, ε.2, Category.comp_id])]
    rfl

  have hTx' : (((sectionIdeal c ε t) ^ r).comap b).IsInvertible := by
    rw [hTcomap]
    exact hTx
  have hDx' : (((E.pullbackAlong t (Category.comp_id t)).I).comap b).IsInvertible := by
    rw [hEx, ← hEx']
    exact hDx
  obtain ⟨eT⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso b hTt hTx'
  haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison b hDt hDx'
  let eD := asIso (((E.pullbackAlong t (Category.comp_id t)).I).pullbackModuleComparison b)

  exact ⟨Scheme.Modules.pullbackTensorObjIso b L _ ≪≫
    (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso b _ _ ≪≫ (eT ⊗ᵢ eD) ≪≫
      (eqToIso (by rw [hTcomap]) ⊗ᵢ eqToIso (by rw [hEx]))))⟩

theorem core
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g r : ℕ) (hgr : 2 * g ≤ r + 1) (hrg : g ≤ r)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ (r - g) + (r - g) < M)
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hσ : ∀ i m, ∃ y : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (B i)), (σ i m).1 = y ≫ z i)
    {ι : Type u} (idx : {a : Fin (r - g) → Fin M // Function.Injective a} → (∀ i, Fin (deg i)) → ι)
    (Dγ : ι → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ a m, (Dγ (idx a m)).I = prodKerGraph c (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k]
    (eB : ∀ i, (B i →ₐ[R] k) ≃ Fin (deg i))
    (s : Spec (CommRingCat.of k) ⟶ T) (hx : s ≫ t = specMap R k)
    (hsm : Smooth (pullback.snd c (specMap R k)))
    (hgoodirr : GeometricallyIrreducible (pullback.snd c (specMap R k)))
    (hgoodU : Set.range (pullback.fst c (specMap R k)).base ⊆ (U : Set C)) :
    ∃ i : ι, ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by
  classical

  let m₀ : ∀ i, Fin (deg i) := fun i => ⟨0, hdeg i⟩
  have heM : r - g ≤ M := (Nat.le_add_left _ _).trans hMlt.le

  by_cases hcov : Nonempty ((pullback c (specMap R k)).TwoAffineOpenCover)
  swap
  · refine ⟨idx ⟨Fin.castLE heM, Fin.castLE_injective heM⟩ m₀, fun 𝒲 => ?_⟩
    exact absurd (nonempty_twoAffineOpenCover_of_fibre c k t s hx 𝒲) hcov
  obtain ⟨𝒱₀⟩ := hcov

  haveI : IsIntegral (pullback c (specMap R k)) :=
    isIntegral_pullback_of_smooth_of_geometricallyIrreducible c k ε hsm hgoodirr
  haveI : IsProper (pullback.snd c (specMap R k)) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (specMap R k)) :=
    smoothOfRelativeDimension_snd_of_range_subset c U (specMap R k) hgoodU

  have hg₀ : Module.finrank k (𝒱₀.sectionsOf (pullback.snd c (specMap R k)) (𝟙_ _)).H1 = g :=
    finrank_H1_unit_eq_of_forall_fibre c k g (hg k (specMap R k)) 𝒱₀
  have hχ : ∀ (v : Fin (r - g) → {q : Spec (CommRingCat.of k) ⟶ pullback c (specMap R k) //
        q ≫ pullback.snd c (specMap R k) = 𝟙 _})
      (𝒱 : (pullback c (specMap R k)).TwoAffineOpenCover),
      (Module.finrank k (𝒱.sectionsOf (pullback.snd c (specMap R k))
          ((((sectionFibrePoint ε (specMap R k)).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf (pullback.snd c (specMap R k))
          ((((sectionFibrePoint ε (specMap R k)).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H1 = 1 := by
    intro v 𝒱
    rw [Scheme.TwoAffineOpenCover.eulerChar_sectionsOf_invModule_pow_ker_tensor_module_prod_ker_eq k
      (pullback.snd c (specMap R k)) g 𝒱₀ hg₀ (sectionFibrePoint ε (specMap R k)).1
      (sectionFibrePoint ε (specMap R k)).2 r v 𝒱]
    omega

  let ψ : SchemeHomOver (specMap R k) t := ⟨s, hx⟩
  let L₀ : (pullback c (specMap R k)).Modules := (L.pullbackAlong ψ).L
  have hL₀ : Scheme.Modules.IsInvertible L₀ := (L.pullbackAlong ψ).isInvertible
  have h0 : IsAlgEquivZero (pullback.snd c (specMap R k)) L₀ :=
    isAlgEquivZero_pullbackAlong_L_of_fibrewiseAlgEquivZero L hL ψ

  obtain ⟨a, ha, hgood⟩ :=
    AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre R c ε B z hz hzdisj
      deg hdeg hdegb r g hgr hMlt k eB 𝒱₀ hg₀ hχ L₀ hL₀ h0
  refine ⟨idx ⟨a, ha⟩ m₀, fun 𝒲 => ?_⟩

  let σs : Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c := fun j => σ (a j) (m₀ (a j))
  have hE : (Dγ (idx ⟨a, ha⟩ m₀)).I = prodKerGraph c (fun j => (σs j).1) (fun j => (σs j).2) := hDγ ⟨a, ha⟩ m₀
  have hσU : ∀ j, Set.range (σs j).1.base ⊆ (U : Set C) := by
    intro j
    obtain ⟨y, hy⟩ := hσ (a j) (m₀ (a j))
    show Set.range (σ (a j) (m₀ (a j))).1.base ⊆ (U : Set C)
    rw [hy]
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hzU (a j) ⟨_, rfl⟩

  let v : Fin (r - g) → {q : Spec (CommRingCat.of k) ⟶ pullback c (specMap R k) //
      q ≫ pullback.snd c (specMap R k) = 𝟙 _} := fun j =>
    ⟨graphOver c (specMap R k ≫ (σs j).1) (by rw [Category.assoc, (σs j).2, Category.comp_id]), graphOver_snd _ _ _⟩
  have hmemv : ∀ j, ∃ φ : B (a j) →ₐ[R] k,
      (v j).1 ≫ pullback.fst c (specMap R k) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z (a j) := fun j =>
    exists_algHom_graphOver_fst_eq c k (z (a j)) (hz (a j)) (σs j) (hσ (a j) (m₀ (a j)))
  have hvan := hgood v hmemv

  have hTt : ((sectionIdeal c ε t) ^ r).IsInvertible :=
    (isInvertible_sectionIdeal_of_range_subset c ε U hεU t).pow r
  have hTx : ((sectionIdeal c ε (specMap R k)) ^ r).IsInvertible :=
    (isInvertible_sectionIdeal_of_range_subset c ε U hεU (specMap R k)).pow r
  have hDt := isInvertible_I_pullbackAlong_of_prodKerGraph c U σs hσU (Dγ (idx ⟨a, ha⟩ m₀)) hE t
  have hDx := isInvertible_I_pullbackAlong_of_prodKerGraph c U σs hσU (Dγ (idx ⟨a, ha⟩ m₀)) hE (specMap R k)

  obtain ⟨e4⟩ := slice4_nonempty_pullback_twist_iso c ε t k s hx L.L r σs (Dγ (idx ⟨a, ha⟩ m₀)) hE hTt hTx hDt hDx

  let F' : (pullback c (specMap R k)).Modules :=
    L₀ ⊗ ((((sectionFibrePoint ε (specMap R k)).1.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)
  let eF : fibreModule c t s (L.L ⊗ (sectionTwist c ε t r ⊗
      ((Dγ (idx ⟨a, ha⟩ m₀)).pullbackAlong t (Category.comp_id t)).idealModule)) ≅
      (Scheme.Modules.pullback (fibreIso c t s (specMap R k) hx).hom).obj F' :=
    fibreModuleIso c t s (specMap R k) hx _ ≪≫ (Scheme.Modules.pullback (fibreIso c t s (specMap R k) hx).hom).mapIso e4
  exact forall_subsingleton_H1_fibre_of_iso c t s (fibreIso c t s (specMap R k) hx) (pullback.snd c (specMap R k))
    (fibreIso_hom_snd c t s (specMap R k) hx) _ F' eF hvan 𝒲

end FltWs11.HCSM

open FltWs11.HCSM in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (g e r : ℕ) (hr : g + e = r) (hgr : 2 * g ≤ r + 1)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ e + e < M)
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hσinj : ∀ i, Function.Injective (σ i))
    (hσ : ∀ i m, ∃ y : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (B i)), (σ i m).1 = y ≫ z i)
    (eB : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] (i : Fin M), (B i →ₐ[R] Ω) ≃ Fin (deg i))
    {ι : Type u} (idx : {a : Fin e → Fin M // Function.Injective a} → (∀ i, Fin (deg i)) → ι)
    (Dγ : ι → RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ a m, (Dγ (idx a m)).I = prodKerGraph c (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) (hsm : Smooth (pullback.snd c (s ≫ t)))
    (hgoodirr : GeometricallyIrreducible (pullback.snd c (s ≫ t))) (hgoodU : Set.range (pullback.fst c (s ≫ t)).base ⊆ (U : Set C)) :
    ∃ i : ι, ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  have hrg : g ≤ r := by omega
  obtain rfl : e = r - g := by omega

  letI : Algebra R k := (Spec.preimage (s ≫ t)).hom.toAlgebra
  have hx : s ≫ t = SmoothProperCurve.specMap R k := by
    change s ≫ t = Spec.map (CommRingCat.ofHom (Spec.preimage (s ≫ t)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [hx] at hsm hgoodirr hgoodU
  exact core R c U ε hεU g r hgr hrg hg B z hz hzU hzdisj deg hdeg hdegb hMlt σ hσ idx Dγ hDγ t L hL k (eB k) s hx
    hsm hgoodirr hgoodU

end
end S_AlgebraicGeometry_RelPicard_exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_forall_subsingleton_H1_sectionsOf_fibreModule_chartModule_of_smooth (solution)
