-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f55170a5-7c41-533a-b4c1-825e4a24e096

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_expand_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicCurve.serrePairing_apply_mk AlgebraicCurve.residueSumOffChartLinear_apply"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (ι : Type) [Fintype ι] (σ : ι → (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) ⟶ X))
    (hσ : 𝔉.twoAffineOpenCover.IsSectional c σ) :
    ∃ (Λ : ι → (𝔉.twoAffineOpenCover.cover c).LaurentChart)
      (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝔉.twoAffineOpenCover.cover c).ρ0
        (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
      (hΛt : ∀ i, (Λ i).HasParameter (𝔉.twoAffineOpenCover.cover c).ρ0)
      (hv : (𝔉.twoAffineOpenCover.cover c).ResiduesVanishOnCoboundaries Λ),
      Function.Bijective ((𝔉.twoAffineOpenCover.cover c).serrePairingInt Λ hv) ∧
        Function.Bijective ((𝔉.twoAffineOpenCover.cover c).serrePairingInt Λ hv).flip := by
  classical

  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) := by
    haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
    exact IsLocalization.AtPrime.isLocalRing ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)})

  have hchart : ∀ i, ∃ Λ : (𝔉.twoAffineOpenCover.cover c).LaurentChart,
      Λ.IsCompletionAlong (𝔉.twoAffineOpenCover.cover c).ρ0
        (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)) ∧
      Λ.HasParameter (𝔉.twoAffineOpenCover.cover c).ρ0 := by
    intro i
    obtain ⟨hfree, hrank⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_cotangent_sectionAlgHom
      (𝒱 := 𝔉.twoAffineOpenCover) (c := c) (σ i) (hσ.comp_eq i) (hσ.range_subset i)
    obtain ⟨t₀, ht₀, hgen⟩ : ∃ t₀ : (𝔉.twoAffineOpenCover.cover c).A0,
        Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i) t₀ = 0 ∧
        RingHom.ker (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)).toRingHom ≤
          Ideal.span {t₀} ⊔ RingHom.ker (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i)
            (hσ.range_subset i)).toRingHom ^ 2 := by

      set φ := Scheme.TwoAffineOpenCover.sectionAlgHom (𝒱 := 𝔉.twoAffineOpenCover) (c := c) (σ i) (hσ.comp_eq i)
        (hσ.range_subset i) with hφ
      set I : Ideal (𝔉.twoAffineOpenCover.cover c).A0 := RingHom.ker φ.toRingHom with hI
      haveI := hfree
      haveI : Module.Finite ↥(GaloisRep.ratLocalizedAt p) I.Cotangent :=
        Module.finite_of_finrank_pos (by rw [hrank]; exact Nat.one_pos)
      let b := Module.finBasisOfFinrankEq ↥(GaloisRep.ratLocalizedAt p) I.Cotangent hrank
      obtain ⟨t, ht⟩ := Ideal.toCotangent_surjective I (b 0)
      refine ⟨(t : (𝔉.twoAffineOpenCover.cover c).A0), RingHom.mem_ker.mp t.2, ?_⟩
      intro y hy
      have hrepr := b.sum_repr (I.toCotangent ⟨y, hy⟩)
      rw [Fin.sum_univ_one] at hrepr
      set cR := b.repr (I.toCotangent ⟨y, hy⟩) 0 with hcR
      have h1 : I.toCotangent (cR • t) = cR • I.toCotangent t := LinearMap.map_smul_of_tower _ cR t
      have h2 : I.toCotangent (⟨y, hy⟩ - cR • t) = 0 := by
        rw [map_sub, h1, ht, hrepr, sub_self]
      have h3 : (((⟨y, hy⟩ : I) - cR • t : I) : (𝔉.twoAffineOpenCover.cover c).A0) ∈ I ^ 2 := (Ideal.toCotangent_eq_zero _ _).mp h2
      have hsplit : y = cR • (t : (𝔉.twoAffineOpenCover.cover c).A0) + (((⟨y, hy⟩ : I) - cR • t : I) : (𝔉.twoAffineOpenCover.cover c).A0) := by
        simp
      rw [hsplit]
      refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right h3)
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨Λ, hΛ, hexp⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_expand_eq
      𝔉.twoAffineOpenCover c σ hσ i t₀ ht₀ hgen
    exact ⟨Λ, hΛ, ⟨t₀, hexp⟩⟩
  choose Λ hΛ hΛt using hchart

  have hv : (𝔉.twoAffineOpenCover.cover c).ResiduesVanishOnCoboundaries Λ :=
    AlgebraicGeometry.SmoothProperCurve.FiniteMapData.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
      p c ε 𝔉 ι σ hσ Λ hΛ hΛt
  refine ⟨Λ, hΛ, hΛt, hv, ?_⟩

  have hπ : Function.Surjective (algebraMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p)) := ZMod.ringHom_surjective _

  have hbc := fun i => AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange 𝔉.twoAffineOpenCover c (ZMod p) (Λ i)
  choose Λk hΛk _huniq _hr0 _hr1 _hp0 _hp1 using hbc
  obtain ⟨σk, hσk, -, hcompk, hpark⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq
      𝔉.twoAffineOpenCover c (ZMod p) σ hσ Λ Λk hΛk

  haveI : IsProper (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p))) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p))) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c _ inferInstance
  haveI : IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p))) := by
    have h := GeometricallyIntegral.geometrically_isIntegral (f := c)
    unfold AlgebraicGeometry.geometrically at h
    exact h (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p)) _ _ (IsPullback.of_hasPullback c _)

  have hvk := AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
    (𝔉.twoAffineOpenCover.pullback c (ZMod p)) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p))) σk hσk Λk
    (fun i => hcompk i (hΛ i)) (fun i => hpark i (hΛt i))
  have hk := AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
    (𝔉.twoAffineOpenCover.pullback c (ZMod p)) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (ZMod p))) σk hσk Λk
    (fun i => hcompk i (hΛ i)) (fun i => hpark i (hΛt i)) hvk

  obtain ⟨g, hfree0, hfin0, -, hfree1, hfin1, -, hbcmod⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
      p c 𝔉.twoAffineOpenCover
  obtain ⟨⟨eH0, heH0⟩, ⟨eH1, heH1⟩⟩ := hbcmod (ZMod p)
  haveI := hfree0; haveI := hfin0; haveI := hfree1; haveI := hfin1
  exact AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective 𝔉.twoAffineOpenCover c hπ Λ Λk hΛk hv hvk
    eH0 heH0 eH1 heH1 hk

end S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional (solution)
