-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fc3a46db-42c1-555d-8fff-8fe63ce12ceb

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicCurve~genus"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.IdealSheafData.top_mul Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelPicard.IsAlgEquivZero Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero"
namespace G0E9
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

noncomputable def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
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

theorem nonempty_invModule_top_iso (X : Scheme.{u}) :
    Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) := by
  have hT : (⊤ : X.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top
  have hN : Scheme.Modules.IsInvertible (⊤ : X.IdealSheafData).invModule := hT.isInvertible_invModule
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hT hT
  have hmul : ((⊤ : X.IdealSheafData) * ⊤).invModule = (⊤ : X.IdealSheafData).invModule := by
    rw [Scheme.IdealSheafData.top_mul]
  obtain ⟨-, ⟨u⟩⟩ := hN.dual
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ u.symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso ((eqToIso hmul).symm ≪≫ e).symm _ ≪≫ u⟩

theorem main
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = 0)
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) :
    Nonempty (M.L ≅ 𝟙_ (pullback c t).Modules) := by

  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsProper (fibreAt c t (𝟙 (Spec (CommRingCat.of K)))) := by
    show IsProper (pullback.snd (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))); infer_instance
  haveI : SmoothOfRelativeDimension 1 (fibreAt c t (𝟙 (Spec (CommRingCat.of K)))) := by
    show SmoothOfRelativeDimension 1 (pullback.snd (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))); infer_instance
  haveI : GeometricallyIrreducible (fibreAt c t (𝟙 (Spec (CommRingCat.of K)))) := by
    show GeometricallyIrreducible (pullback.snd (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))); infer_instance
  haveI : IsIso (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))) := inferInstance

  obtain ⟨L, _, _, Mo, e, he, -, -, -⟩ := SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed R c K t
  obtain ⟨U, V, hU, hV, hUV, hsup⟩ :=
    AlgebraicCurve.exists_isAffineOpen_sup_eq_top Mo.toBase Mo.finset_subset_affineOpen
  let 𝒱M : Mo.C.TwoAffineOpenCover := ⟨U, V, hU, hV, hsup, hUV⟩
  let ψ : pullback (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K))) ≅ Mo.C :=
    asIso (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))) ≪≫ e.symm
  have hψ : ψ.hom ≫ Mo.toBase = fibreAt c t (𝟙 (Spec (CommRingCat.of K))) := by
    show (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K))) ≫ e.inv) ≫ Mo.toBase =
      pullback.snd (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))
    rw [← he, Category.assoc, e.inv_hom_id_assoc,
      pullback.condition (f := pullback.snd c t) (g := 𝟙 (Spec (CommRingCat.of K))), Category.comp_id]
  obtain ⟨𝒲, -, -, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (fibreAt c t (𝟙 (Spec (CommRingCat.of K))))
      Mo.toBase ψ hψ 𝒱M (𝟙_ Mo.C.Modules) ((Scheme.Modules.pullback ψ.hom).obj (𝟙_ Mo.C.Modules)) (Iso.refl _)

  obtain ⟨-, hfin⟩ :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero R c ε 0 hg M hM 0
      (by norm_num) K (𝟙 (Spec (CommRingCat.of K))) 𝒲
  have h1 : Module.finrank K
      (𝒲.sectionsOf (fibreAt c t (𝟙 (Spec (CommRingCat.of K))))
        (fibreModule c t (𝟙 (Spec (CommRingCat.of K))) (M.L ⊗ sectionTwist c ε t 0))).H0 = 1 := hfin
  haveI := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒲.sectionsOf (fibreAt c t (𝟙 (Spec (CommRingCat.of K))))
    (fibreModule c t (𝟙 (Spec (CommRingCat.of K))) (M.L ⊗ sectionTwist c ε t 0))).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲
    (fibreAt c t (𝟙 (Spec (CommRingCat.of K)))) (fibreModule c t (𝟙 (Spec (CommRingCat.of K))) (M.L ⊗ sectionTwist c ε t 0))
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  obtain ⟨s', hs'⟩ := exists_hom_ne_zero _ (eΓ.symm y) hσ

  have h0 : sectionTwist c ε t 0 = (⊤ : (pullback c t).IdealSheafData).invModule := by
    show ((sectionIdeal c ε t) ^ 0).invModule = _
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
  obtain ⟨uT⟩ := nonempty_invModule_top_iso (pullback c t)
  let uL : fibreModule c t (𝟙 (Spec (CommRingCat.of K))) (M.L ⊗ sectionTwist c ε t 0) ≅
      fibreModule c t (𝟙 (Spec (CommRingCat.of K))) M.L :=
    (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K))))).mapIso
      (whiskerLeftIso M.L (eqToIso h0 ≪≫ uT) ≪≫ ρ_ M.L)
  have hs : s' ≫ uL.hom ≠ 0 := by
    intro h
    apply hs'
    rw [← Category.comp_id s', ← uL.hom_inv_id, ← Category.assoc, h, zero_comp]

  have hL₀ : Scheme.Modules.IsInvertible (fibreModule c t (𝟙 (Spec (CommRingCat.of K))) M.L) :=
    M.isInvertible.pullback _
  have hA : IsAlgEquivZero (fibreAt c t (𝟙 (Spec (CommRingCat.of K))))
      (fibreModule c t (𝟙 (Spec (CommRingCat.of K))) M.L) := hM K (𝟙 _)
  obtain ⟨eN⟩ := RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero
    (fibreAt c t (𝟙 (Spec (CommRingCat.of K)))) 𝒲 hL₀ hA (s' ≫ uL.hom) hs

  exact ⟨((Scheme.Modules.pullbackId _).app M.L).symm ≪≫
    (Scheme.Modules.pullbackCongr
      (IsIso.inv_hom_id (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K))))).symm).app M.L ≪≫
    ((Scheme.Modules.pullbackComp (inv (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))))
      (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K))))).app M.L).symm ≪≫
    (Scheme.Modules.pullback (inv (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))))).mapIso eN ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (inv (pullback.fst (pullback.snd c t) (𝟙 (Spec (CommRingCat.of K)))))⟩

end AlgebraicGeometry.RelPicard.G0E9

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = 0)
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) :
    Nonempty (M.L ≅ 𝟙_ (pullback c t).Modules) :=
  AlgebraicGeometry.RelPicard.G0E9.main R c ε hg K t M hM

end S_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero (solution)
