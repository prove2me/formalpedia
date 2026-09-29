-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/63c4c666-447a-5347-bef3-821779d68b1b

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_exists_iso_pointsSubBasepointModule
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4"
p2m_attr_erase "simp" "ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst exteriorPower.mulₗ_apply_coe PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicCurve GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero SmoothProperCurve.FiniteMapData RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso toProdSpec fstPullbackToProdSpecPullbackIso pointSubBasepointModule pointsSubBasepointModule thetaBundle IsAlgEquivZero.exists_iso_pointsSubBasepointModule nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso"
namespace ThetaLinear
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

section
variable {T : Scheme.{u}}

noncomputable def mid4 (W X Y Z : T.Modules) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ _ _ _ ≪≫ whiskerLeftIso W ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ _ _ _) ≪≫ (α_ _ _ _).symm

noncomputable def swapRight (W X B : T.Modules) : (W ⊗ X) ⊗ B ≅ (W ⊗ B) ⊗ X :=
  α_ _ _ _ ≪≫ whiskerLeftIso W (β_ X B) ≪≫ (α_ _ _ _).symm

theorem nonempty_iso_of_tensor_iso {X Y B : T.Modules} (hB : Scheme.Modules.IsInvertible B)
    (e : X ⊗ B ≅ Y ⊗ B) : Nonempty (X ≅ Y) := by
  obtain ⟨-, ⟨d⟩⟩ := hB.dual
  exact ⟨(ρ_ X).symm ≪≫ whiskerLeftIso X d.symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso e _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso Y d ≪≫ ρ_ Y⟩

end

section
variable {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}

noncomputable def ptsAppendIso [IsSeparated c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∀ (Ps Qs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      pointsSubBasepointModule (a := c) ε (Ps ++ Qs) ≅
        pointsSubBasepointModule (a := c) ε Ps ⊗ pointsSubBasepointModule (a := c) ε Qs
  | [], Qs => (λ_ _).symm
  | P :: Ps, Qs => whiskerLeftIso (pointSubBasepointModule (a := c) P ε) (ptsAppendIso ε Ps Qs) ≪≫ (α_ _ _ _).symm

noncomputable abbrev corr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)) : T.Modules :=
  Ps.foldr (fun P A => (Scheme.Modules.pullback (rigSection c t P)).obj F ⊗ A) (𝟙_ T.Modules)

noncomputable def corrAppendIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules) :
    ∀ (Ps Qs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      corr t F (Ps ++ Qs) ≅ corr t F Ps ⊗ corr t F Qs
  | [], Qs => (λ_ _).symm
  | P :: Ps, Qs => whiskerLeftIso ((Scheme.Modules.pullback (rigSection c t P)).obj F) (corrAppendIso t F Ps Qs) ≪≫
      (α_ _ _ _).symm

theorem isInvertible_corr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules)
    (hF : Scheme.Modules.IsInvertible F) :
    ∀ (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)), Scheme.Modules.IsInvertible (corr t F Ps)
  | [] => Scheme.Modules.isInvertible_unit T
  | P :: Ps => (hF.pullback _).tensor (isInvertible_corr t F hF Ps)

end

end AlgebraicGeometry.RelPicard.ThetaLinear

open AlgebraicGeometry.RelPicard.ThetaLinear in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (s : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra k' L] (M : CurveModel k' L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k' L) (g' : ℕ),
      (∀ D : Divisor k' L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    (N₁ N₂ : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (hN₁ : FibrewiseAlgEquivZero N₁) (hN₂ : FibrewiseAlgEquivZero N₂)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N₁.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        thetaBundle c ε t (M.tensor (N₂.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ≅
      thetaBundle c ε t (M.tensor ((N₁.tensor N₂).pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        thetaBundle c ε t M r (r + 1 - g)) := by
  let S := Spec (CommRingCat.of k)

  have h0 : ∀ (N : RigidifiedLineBundle c ε (𝟙 S)), FibrewiseAlgEquivZero N →
      IsAlgEquivZero c ((Scheme.Modules.pullback (toProdSpec c)).obj N.L) := by
    intro N hN
    let e : C ⟶ pullback (pullback.snd c (𝟙 S)) (𝟙 S) :=
      pullback.lift (toProdSpec c) c (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
    have he : e ≫ fibreAt c (𝟙 S) (𝟙 S) = c := pullback.lift_snd _ _ _
    have hfst : e ≫ pullback.fst (pullback.snd c (𝟙 S)) (𝟙 S) = toProdSpec c := pullback.lift_fst _ _ _
    refine IsAlgEquivZero.of_iso ?_ ((hN k (𝟙 S)).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app N.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app N.L
  have rep : ∀ (N : RigidifiedLineBundle c ε (𝟙 S)), FibrewiseAlgEquivZero N →
      ∃ Ps : List (SchemeHomOver (𝟙 S) c), Nonempty (N.L ≅ pointsSubBasepointModule (a := c) ε Ps) := by
    intro N hN
    obtain ⟨Ps, ⟨e⟩⟩ :=
      RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule ε h𝔉 (N.isInvertible.pullback _) (h0 N hN)
    exact ⟨Ps, ⟨(fstPullbackToProdSpecPullbackIso c N.L).symm ≪≫ e⟩⟩
  obtain ⟨Ps₁, ⟨e₁⟩⟩ := rep N₁ hN₁
  obtain ⟨Ps₂, ⟨e₂⟩⟩ := rep N₂ hN₂
  have e₁₂ : (N₁.tensor N₂).L ≅ pointsSubBasepointModule (a := c) ε (Ps₁ ++ Ps₂) :=
    (e₁ ⊗ᵢ e₂) ≪≫ (ptsAppendIso ε Ps₁ Ps₂).symm

  obtain ⟨φ₁⟩ := RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso k c ε h𝔉 g hg
    M hM Ps₁ N₁ hN₁ e₁ r hr
  obtain ⟨φ₂⟩ := RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso k c ε h𝔉 g hg
    M hM Ps₂ N₂ hN₂ e₂ r hr
  obtain ⟨φ₁₂⟩ := RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso k c ε h𝔉 g hg
    M hM (Ps₁ ++ Ps₂) (N₁.tensor N₂) (hN₁.tensor hN₂) e₁₂ r hr

  have hB : Scheme.Modules.IsInvertible (corr t M.L Ps₁ ⊗ corr t M.L Ps₂) :=
    (isInvertible_corr t M.L M.isInvertible Ps₁).tensor (isInvertible_corr t M.L M.isInvertible Ps₂)
  refine nonempty_iso_of_tensor_iso hB ?_
  refine mid4 _ _ _ _ ≪≫ (φ₁ ⊗ᵢ φ₂) ≪≫ ?_
  refine (whiskerRightIso (whiskerLeftIso _ (corrAppendIso t M.L Ps₁ Ps₂).symm ≪≫ φ₁₂) _).symm ≪≫ ?_
  exact (swapRight _ _ _).symm

end S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero (solution)
