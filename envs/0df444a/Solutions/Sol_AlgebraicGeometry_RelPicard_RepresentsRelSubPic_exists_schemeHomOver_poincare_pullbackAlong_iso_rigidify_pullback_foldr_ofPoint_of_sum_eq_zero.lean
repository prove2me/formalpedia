-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9ead8576-b386-55b9-aa4c-ef5de905e445

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace RTwistK5

section foldr
variable {X : Scheme.{u}} {ι : Type*}

abbrev twistStep (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (M : X.Modules) : X.Modules :=
  (K i ^ pos i).invModule ⊗ (K i ^ neg i).module ⊗ M

def foldrTwistCongr (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅ l.foldr (twistStep K pos neg) M'
  | [], _, _, e => e
  | (i :: l), _, _, e => whiskerLeftIso _ (whiskerLeftIso _ (foldrTwistCongr K pos neg l e))

theorem isInvertible_pow {I : X.IdealSheafData} (hI : I.IsInvertible) : ∀ n : ℕ, (I ^ n).IsInvertible
  | 0 => by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | (n + 1) => by
    rw [pow_succ]
    exact (isInvertible_pow hI n).mul hI

theorem top_pow (n : ℕ) : (⊤ : X.IdealSheafData) ^ n = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

theorem isInvertible_foldrTwist (K : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (hK : ∀ i, (K i).IsInvertible) :
    ∀ (l : List ι) {M : X.Modules} (_ : Scheme.Modules.IsInvertible M),
      Scheme.Modules.IsInvertible (l.foldr (twistStep K pos neg) M)
  | [], _, hM => hM
  | (i :: l), _, hM =>
    (isInvertible_pow (hK i) (pos i)).isInvertible_invModule.tensor
      ((isInvertible_pow (hK i) (neg i)).isInvertible_module.tensor (isInvertible_foldrTwist K pos neg hK l hM))

end foldr

section top
variable {X : Scheme.{u}}

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (V : Z.Opens) :
    Subsingleton Γ(Z, V) := by
  obtain rfl : V = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

theorem unitToPushforwardUnit_eq_zero_of_isEmpty {Z : Scheme.{u}} (i : Z ⟶ X) [IsEmpty Z] :
    i.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  haveI : Subsingleton Γ(Z, i ⁻¹ᵁ U.unop) := subsingleton_sections_of_isEmpty _
  exact Subsingleton.elim (α := Γ(Z, i ⁻¹ᵁ U.unop)) _ _

def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (unitToPushforwardUnit_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι) ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

theorem nonempty_topInvModuleIso : Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) :=
  MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit (topModuleIso (X := X))
    (Scheme.IdealSheafData.isInvertible_top (X := X)).nonempty_module_tensor_invModule_iso.1 ⟨λ_ _⟩

def topInvModuleIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules := nonempty_topInvModuleIso.some

def twistStepTopIso {ι : Type*} (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = ⊤)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ M' :=
  ((eqToIso (by rw [hi, top_pow]) : (K i ^ pos i).invModule ≅ (⊤ : X.IdealSheafData).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi, top_pow]) : (K i ^ neg i).module ≅ (⊤ : X.IdealSheafData).module) ⊗ᵢ e)) ≪≫
    ((topInvModuleIso ⊗ᵢ (topModuleIso ⊗ᵢ Iso.refl M')) ≪≫ ((λ_ _) ≪≫ (λ_ _)))

def twistStepCongr {ι : Type*} (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = K' i)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ twistStep K' pos neg i M' :=
  ((eqToIso (by rw [hi]) : (K i ^ pos i).invModule ≅ (K' i ^ pos i).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi]) : (K i ^ neg i).module ≅ (K' i ^ neg i).module) ⊗ᵢ e))

def foldrTwistSelectIso {ι : Type*} {κ : Type*} [DecidableEq κ] (c : ι → κ) (j : κ)
    (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (h₁ : ∀ i, c i = j → K i = K' i) (h₂ : ∀ i, c i ≠ j → K i = ⊤) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅
        l.foldr (fun i N => if c i = j then twistStep K' pos neg i N else N) M'
  | [], _, _, e => e
  | (i :: l), M, M', e => by
    by_cases hc : c i = j
    · refine twistStepCongr K K' pos neg i (h₁ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_pos hc]
    · refine twistStepTopIso K pos neg i (h₂ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_neg hc]

end top

section geom
variable {X₀ X T : Scheme.{u}}

theorem comap_ker_eq_ker_of_isPullback {Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem comap_ker_hom_of_iso (e : X₀ ≅ X) (y : T ⟶ X) [IsClosedImmersion y] :
    y.ker.comap e.hom = (y ≫ e.inv).ker :=
  comap_ker_eq_ker_of_isPullback (iX := y ≫ e.inv) (g := 𝟙 T) (IsPullback.of_vert_isIso ⟨by simp⟩)

theorem isIso_snd_of_subset_range (χ : X₀ ⟶ X) [IsClosedImmersion χ] [IsReduced X] (U : X.Opens)
    (hU : (U : Set X) ⊆ Set.range χ.base) : IsIso (pullback.snd χ U.ι) := by
  haveI : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  haveI : Surjective (pullback.snd χ U.ι) := ⟨by
    intro u
    have h1 : U.ι.base u ∈ Set.range χ.base :=
      hU (by rw [← Scheme.Opens.range_ι U]; exact ⟨u, rfl⟩)
    have h2 : u ∈ Set.range (pullback.snd χ U.ι).base := by
      rw [Scheme.Pullback.range_snd]; exact h1
    exact h2⟩
  exact isIso_of_isClosedImmersion_of_surjective _

theorem isPullback_of_subset_range (χ : X₀ ⟶ X) [IsClosedImmersion χ] [IsReduced X] (U : X.Opens)
    (hU : (U : Set X) ⊆ Set.range χ.base) (y : T ⟶ X) (hy : Set.range y.base ⊆ (U : Set X))
    (z : T ⟶ X₀) (hz : z ≫ χ = y) : IsPullback z (𝟙 T) χ y := by
  have hy' : Set.range y.base ⊆ Set.range U.ι.base := by rwa [Scheme.Opens.range_ι]
  obtain ⟨y', rfl⟩ : ∃ y' : T ⟶ U, y' ≫ U.ι = y :=
    ⟨IsOpenImmersion.lift U.ι y hy', IsOpenImmersion.lift_fac _ _ _⟩
  haveI := isIso_snd_of_subset_range χ U hU
  haveI : IsIso ((pullbackLeftPullbackSndIso χ U.ι y').hom ≫ pullback.snd χ (y' ≫ U.ι)) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
    infer_instance
  haveI : IsIso (pullback.snd χ (y' ≫ U.ι)) :=
    IsIso.of_isIso_comp_left (pullbackLeftPullbackSndIso χ U.ι y').hom (pullback.snd χ (y' ≫ U.ι))
  let l : T ⟶ pullback χ (y' ≫ U.ι) := pullback.lift z (𝟙 T) (by rw [hz, Category.id_comp])
  have hl : l ≫ pullback.snd _ _ = 𝟙 T := pullback.lift_snd _ _ _
  haveI : IsIso (l ≫ pullback.snd _ _) := by rw [hl]; infer_instance
  haveI : IsIso l := IsIso.of_isIso_comp_right l (pullback.snd _ _)
  exact IsPullback.of_iso_pullback ⟨by rw [hz, Category.id_comp]⟩ (asIso l)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem ker_eq_top_of_isEmpty (f : X₀ ⟶ X) [QuasiCompact f] [IsEmpty X₀] : f.ker = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  have hx' : x ∈ closure (Set.range f.base) := by
    rw [← Scheme.Hom.support_ker]; exact hx
  rw [Set.range_eq_empty, closure_empty] at hx'
  exact hx'

theorem comap_ker_eq_top_of_disjoint (χ : X₀ ⟶ X) (y : T ⟶ X) [IsClosedImmersion y]
    (h : ∀ (t : T) (x₀ : X₀), χ.base x₀ ≠ y.base t) : y.ker.comap χ = ⊤ := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  haveI : IsEmpty ↥(pullback χ y) := ⟨fun q => h ((pullback.snd χ y).base q) ((pullback.fst χ y).base q) (by
    have := congrArg (fun g => g.base q) (pullback.condition (f := χ) (g := y))
    simpa using this)⟩
  exact ker_eq_top_of_isEmpty _

end geom

end RTwistK5

end

theorem solution
    {R₀ R B : Type u} [CommRing R₀] [CommRing R] [CommRing B] (φ : R₀ →+* R) (ρ : R →+* B)
    {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c} (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R₀)) [IsProper y] [SmoothOfRelativeDimension 1 y]
    (hgi : ∀ (k : Type u) [Field k] [IsAlgClosed k] (u : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀)),
      GeometricallyIntegral (pullback.snd y u))
    (f : X ⟶ Y) (hf : f ≫ y = c ≫ Spec.map (CommRingCat.ofHom φ))
    (fB : pullback c (Spec.map (CommRingCat.ofHom ρ)) ⟶ pullback y (Spec.map (CommRingCat.ofHom (ρ.comp φ))))
    (hfB₁ : fB ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f)
    (hfB₂ : fB ≫ pullback.snd _ _ = pullback.snd _ _)
    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ.comp φ))) y)
    (pos neg : Fin n → ℕ) (hdeg : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0) :
    ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong a).L ≅
        Scheme.Modules.rigidify (rigSection c (Spec.map (CommRingCat.ofHom ρ)) ε) (pullback.snd c (Spec.map (CommRingCat.ofHom ρ)))
          ((Scheme.Modules.pullback fB).obj
            ((List.finRange n).foldr
              (fun i N => ((RelEffCartierDiv.ofPoint y (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
                ((RelEffCartierDiv.ofPoint y (s i).1 (s i).2).I ^ (neg i)).module ⊗ N)
              (𝟙_ (pullback y (Spec.map (CommRingCat.ofHom (ρ.comp φ)))).Modules)))) := by
  classical

  let tA : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ρ)
  let tB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R₀) := Spec.map (CommRingCat.ofHom (ρ.comp φ))
  have htAB : tA ≫ Spec.map (CommRingCat.ofHom φ) = tB := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfB₁' : fB ≫ pullback.fst y tB = pullback.fst c tA ≫ f := hfB₁
  have hfB₂' : fB ≫ pullback.snd y tB = pullback.snd c tA := hfB₂

  let K : Fin n → (pullback y tB).IdealSheafData := fun i => (RelEffCartierDiv.ofPoint y (s i).1 (s i).2).I
  haveI hstab : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd y tB) := MorphismProperty.pullback_snd y tB inferInstance
  have hKinv : ∀ i, (K i).IsInvertible := fun i =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd y tB) (graphOver y (s i).1 (s i).2) (graphOver_snd _ _ _)
  let T : (pullback y tB).Modules := (List.finRange n).foldr (RTwistK5.twistStep K pos neg) (𝟙_ _)
  have hTinv : Scheme.Modules.IsInvertible T :=
    RTwistK5.isInvertible_foldrTwist K pos neg hKinv _ (Scheme.Modules.isInvertible_unit _)

  have hTXinv : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback fB).obj T) := hTinv.pullback fB
  let Mr : RigidifiedLineBundle c ε tA := RigidifiedLineBundle.ofInvertible (ε := ε) _ hTXinv

  have hAEZ : FibrewiseAlgEquivZero Mr := by
    intro k _ _ sk
    obtain ⟨erig⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
      (rigSection c tA ε) (pullback.snd c tA) _ hTXinv k sk
    refine IsAlgEquivZero.of_iso erig.symm ?_

    let σ' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀) := sk ≫ tB
    let c' := pullback.snd y σ'
    haveI : IsProper c' := inferInstance
    haveI : SmoothOfRelativeDimension 1 c' := MorphismProperty.pullback_snd y σ' inferInstance
    haveI : SmoothOfRelativeDimension 1 (pullback.snd c' (𝟙 (Spec (CommRingCat.of k)))) :=
      MorphismProperty.pullback_snd c' (𝟙 _) inferInstance
    haveI : GeometricallyIntegral c' := hgi k σ'

    have hxc : ∀ i, (sk ≫ (s i).1) ≫ y = σ' := fun i => by rw [Category.assoc, (s i).2]
    let x : Fin n → (Spec (CommRingCat.of k) ⟶ pullback y σ') := fun i => graphOver y (sk ≫ (s i).1) (hxc i)
    have hx₁ : ∀ i, x i ≫ pullback.fst _ _ = sk ≫ (s i).1 := fun i => graphOver_fst _ _ _
    have hx : ∀ i, x i ≫ c' = 𝟙 _ := fun i => graphOver_snd _ _ _

    let ψ : SchemeHomOver σ' tB := ⟨sk, rfl⟩
    let Φ₂ : pullback y σ' ⟶ pullback y tB := baseChangeSnd y ψ
    let pr : pullback c' (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback y σ' := pullback.fst c' (𝟙 _)
    let Φ := pr ≫ Φ₂
    let K' : Fin n → (pullback c' (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun i =>
      (RelEffCartierDiv.ofPoint c' (x i) (hx i)).I

    have hab : ∀ i, (K i).comap Φ₂ = (x i).ker := by
      intro i
      have ha : (K i).comap Φ₂ =
          (graphOver y (ψ.1 ≫ (s i).1) (by rw [Category.assoc, (s i).2, ψ.2])).ker :=
        congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint y (s i).1 (s i).2 ψ.1 ψ.2)
      rw [ha]

    have hgeo : ∀ i, (x i).ker.comap pr = K' i := by
      intro i
      have sq : CommSq (graphOver c' (x i) (hx i)) (𝟙 _) pr (x i) := ⟨by rw [Category.id_comp]; exact graphOver_fst _ _ _⟩
      exact RTwistK5.comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)
    have hKΦ : ∀ i, (K i).comap Φ = K' i := by
      intro i
      rw [Scheme.IdealSheafData.comap_comp, hab, hgeo i]
    have hK'inv : ∀ i, ((K i).comap Φ).IsInvertible := by
      intro i; rw [hKΦ]
      exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' (𝟙 _)) (graphOver c' (x i) (hx i)) (graphOver_snd _ _ _)

    have h1inv : ∀ (Z : Scheme.{u}), (1 : Z.IdealSheafData).IsInvertible := fun Z => by
      rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
    let C0 : Fin 0 → (pullback y tB).IdealSheafData := fun _ => ⊤
    let a0 : Fin 0 → ℕ := fun _ => 0
    have hprod : (∏ F, C0 F ^ a0 F) = 1 := Fintype.prod_empty _
    have hprod' : (∏ F, (C0 F).comap Φ ^ a0 F) = 1 := Fintype.prod_empty _
    obtain ⟨eB⟩ : Nonempty ((∏ F, C0 F ^ a0 F).invModule ⊗ (∏ F, C0 F ^ a0 F).module ≅ 𝟙_ _) := by
      rw [hprod]; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
    obtain ⟨eB'⟩ : Nonempty ((∏ F, (C0 F).comap Φ ^ a0 F).invModule ⊗ (∏ F, (C0 F).comap Φ ^ a0 F).module ≅ 𝟙_ _) := by
      rw [hprod']; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
    obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso Φ K pos neg C0 a0 a0 hKinv
      (fun F => F.elim0) hK'inv (fun F => F.elim0)
    let c0 : Fin n → Fin 1 := fun _ => 0
    have eN : (Scheme.Modules.pullback Φ).obj ((List.finRange n).foldr (RTwistK5.twistStep K pos neg) (𝟙_ _)) ≅
        (List.finRange n).foldr (fun i N => if c0 i = 0 then RTwistK5.twistStep K' pos neg i N else N) (𝟙_ _) :=
      (Scheme.Modules.pullback Φ).mapIso (RTwistK5.foldrTwistCongr K pos neg _ eB.symm) ≪≫ e4 ≪≫
        RTwistK5.foldrTwistCongr _ pos neg _ eB' ≪≫
        RTwistK5.foldrTwistSelectIso c0 0 (fun i => (K i).comap Φ) K' pos neg (fun i _ => hKΦ i) (fun i h => absurd rfl h) _ (Iso.refl _)

    have hdeg' : (∑ i ∈ Finset.univ.filter (fun i => c0 i = 0), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
      rw [Finset.filter_true_of_mem (fun _ _ => rfl)]; exact hdeg
    have hS := AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero c' x hx (fun i => c0 i = 0) pos neg hdeg'
    have hY : IsAlgEquivZero (pullback.snd c' (𝟙 _)) ((Scheme.Modules.pullback Φ).obj T) := hS.of_iso eN.symm

    have comm₂ : (pullback.fst (pullback.snd c tA) sk ≫ pullback.fst c tA ≫ f) ≫ y =
        pullback.snd (pullback.snd c tA) sk ≫ σ' := by
      simp only [Category.assoc]
      rw [hf]
      change _ = pullback.snd (pullback.snd c tA) sk ≫ sk ≫ tB
      rw [← htAB, pullback.condition_assoc, pullback.condition_assoc]
    let g₂ : pullback (pullback.snd c tA) sk ⟶ pullback y σ' := pullback.lift _ _ comm₂
    let g : pullback (pullback.snd c tA) sk ⟶ pullback c' (𝟙 (Spec (CommRingCat.of k))) :=
      pullback.lift g₂ (pullback.snd _ sk) (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
    have hg : g ≫ pullback.snd c' (𝟙 _) = fibreAt c tA sk := pullback.lift_snd _ _ _
    have hΦ₂f : Φ₂ ≫ pullback.fst y tB = pullback.fst y σ' := by
      simp only [Φ₂, baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have hΦ₂s : Φ₂ ≫ pullback.snd y tB = pullback.snd y σ' ≫ sk := by
      simp only [Φ₂, baseChangeSnd, pullback.lift_snd]
      rfl
    have hg1 : g ≫ pr = g₂ := pullback.lift_fst _ _ _
    have hg2f : g₂ ≫ pullback.fst y σ' = pullback.fst _ sk ≫ pullback.fst c tA ≫ f := pullback.lift_fst _ _ _
    have hg2s : g₂ ≫ pullback.snd y σ' = pullback.snd _ sk := pullback.lift_snd _ _ _
    have hgΦ : g ≫ Φ = pullback.fst (pullback.snd c tA) sk ≫ fB := by
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [hfB₁']
        change g ≫ pr ≫ Φ₂ ≫ pullback.fst y tB = _
        rw [hΦ₂f, ← Category.assoc g pr, hg1, hg2f]
      · simp only [Category.assoc]
        rw [hfB₂']
        change g ≫ pr ≫ Φ₂ ≫ pullback.snd y tB = _
        rw [hΦ₂s, ← Category.assoc g pr, hg1, ← Category.assoc, hg2s, pullback.condition]
    have hF := hY.pullback g hg
    exact hF.of_iso ((Scheme.Modules.pullbackComp g Φ).app _ ≪≫ (Scheme.Modules.pullbackCongr hgΦ).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm)

  obtain ⟨a, ha, -⟩ := hD.univ tA Mr hAEZ
  exact ⟨a, ha⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero (solution)
