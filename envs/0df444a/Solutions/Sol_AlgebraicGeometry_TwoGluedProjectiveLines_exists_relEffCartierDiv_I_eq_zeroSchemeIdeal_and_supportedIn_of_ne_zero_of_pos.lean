-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedProjectiveLines.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1d01ff9b-aea4-5f12-9191-4a67ee5c1bfd

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_TwoChartCech_GluedLines
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
import Theorems.Thm_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections
import Theorems.Thm_TwoChartCech_finrank_H0_gluedLinesSections_zero_zero_le_one
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve~H1~genus~cechDiff"

section G1
open TopologicalSpace Opposite
namespace FltWs21
namespace M16G1

variable {X : Scheme.{u}} {M : X.Modules}

theorem app_map {N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  simpa using ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

theorem map_toUnitSection_one {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection U 1) = Scheme.Modules.toUnitSection V 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem eq_smul_toUnitSection_one {U : X.Opens} (m : Γ(𝟙_ X.Modules, U)) :
    m = Scheme.Modules.ofUnitSection U m • Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]

theorem eq_zero_of_forall_app_one (φ : 𝟙_ X.Modules ⟶ M)
    (h : ∀ U : X.Opens, φ.app U (Scheme.Modules.toUnitSection U 1) = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  ext m
  rw [eq_smul_toUnitSection_one m, Scheme.Modules.Hom.app_smul, h U, smul_zero]
  rfl

theorem eq_zero_of_app_top_one (φ : 𝟙_ X.Modules ⟶ M)
    (h : φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = 0) : φ = 0 := by
  apply eq_zero_of_forall_app_one
  intro U
  rw [← map_toUnitSection_one (homOfLE (le_top : U ≤ ⊤)), app_map, h, map_zero]

theorem isFrameOn_app_of_iso {N : X.Modules} (φ : M ≅ N) {U V : X.Opens} {s : Γ(M, U)}
    (h : Scheme.Modules.IsFrameOn s V) : Scheme.Modules.IsFrameOn (φ.hom.app U s) V := by
  intro W hWU hWV
  have e : ∀ g : Γ(X, W), g • N.presheaf.map (homOfLE hWU).op (φ.hom.app U s) =
      φ.hom.app W (g • M.presheaf.map (homOfLE hWU).op s) := by
    intro g
    rw [Scheme.Modules.Hom.app_smul, app_map]
  have hb : Function.Bijective (fun x : Γ(M, W) => φ.hom.app W x) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨fun y => φ.inv.app W y, fun x => ?_, fun y => ?_⟩
    · show φ.inv.app W (φ.hom.app W x) = x
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
      rfl
    · show φ.hom.app W (φ.inv.app W y) = y
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
      rfl
  have : (fun g : Γ(X, W) => g • N.presheaf.map (homOfLE hWU).op (φ.hom.app U s)) =
      (fun x : Γ(M, W) => φ.hom.app W x) ∘ (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) := by
    funext g; exact e g
  rw [this]
  exact hb.comp (h hWU hWV)

theorem unitSection_eq_toUnitSection (U : X.Opens) :
    Scheme.Modules.unitSection U = Scheme.Modules.toUnitSection U 1 := rfl

theorem eq_zero_or_support_zeroSchemeIdeal_eq_empty {Y : Scheme.{u}} {N : Y.Modules}
    (hN : Scheme.Modules.IsInvertible N) (e : N ≅ 𝟙_ Y.Modules)
    (hΓ : ∀ f : Γ(Y, ⊤), f = 0 ∨ IsUnit f) (τ : 𝟙_ Y.Modules ⟶ N) :
    τ = 0 ∨ ((Scheme.Modules.zeroSchemeIdeal τ).support : Set Y) = ∅ := by

  set Ω : Γ(N, ⊤) := e.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with hΩdef
  have hΩ : Scheme.Modules.IsFrameOn Ω (⊤ : Y.Opens) := by
    have := isFrameOn_app_of_iso e.symm (U := ⊤) (Scheme.Modules.isFrameOn_unitSection (U := (⊤ : Y.Opens)) (⊤ : Y.Opens))
    simp [unitSection_eq_toUnitSection] at this
    exact this
  set f : Γ(Y, ⊤) := Scheme.Modules.ofUnitSection ⊤ (e.hom.app ⊤ (τ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) with hfdef
  have hτ : τ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = f • Ω := by
    have h1 := eq_smul_toUnitSection_one (e.hom.app ⊤ (τ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)))
    have h2 := congrArg (fun m => e.inv.app ⊤ m) h1
    simp only at h2
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app] at h2
    rw [Scheme.Modules.Hom.app_smul] at h2
    exact h2
  rcases hΓ f with hf | hf
  · left
    apply eq_zero_of_app_top_one
    rw [hτ, hf, zero_smul]
  · right

    have hI : ∀ U : Y.affineOpens, (Scheme.Modules.zeroSchemeIdeal τ).ideal U = ⊤ := by
      intro U
      rw [AlgebraicGeometry.Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul hN Ω hΩ τ f hτ U le_top,
        Ideal.span_singleton_eq_top]
      exact hf.map _
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) (show x ∈ (⊤ : Y.Opens) from trivial)
    have h := (Scheme.IdealSheafData.mem_support_iff.mp hx) ⟨U, hU⟩
    rw [hI ⟨U, hU⟩] at h
    have : x ∉ Y.basicOpen (1 : Γ(Y, U)) := (Y.mem_zeroLocus_iff _ _).mp h 1 trivial
    apply this
    rw [Y.basicOpen_of_isUnit isUnit_one]
    exact hxU

theorem zero_or_isUnit_of_finrank_H0_eq_one {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (.of k))
    (𝒱 : Y.TwoAffineOpenCover) [Nontrivial Γ(Y, ⊤)]
    (h1 : Module.finrank k (𝒱.sectionsOf y (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).H0 = 1) :
    ∀ f : Γ(Y, ⊤), f = 0 ∨ IsUnit f := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom y (⊤ : Y.Opens)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom y (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 y (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)
  have hΓ1 : Module.finrank k Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), ⊤) = 1 := by
    rw [e.finrank_eq, h1]

  set u₀ : Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), ⊤) := Scheme.Modules.toUnitSection ⊤ 1 with hu₀
  have hu₀0 : u₀ ≠ 0 := by
    intro h0
    have := congrArg (Scheme.Modules.ofUnitSection ⊤) h0
    rw [hu₀, Scheme.Modules.ofUnitSection_toUnitSection] at this
    exact one_ne_zero (this.trans (by rfl))
  intro f
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' u₀ hu₀0).mp hΓ1 (Scheme.Modules.toUnitSection ⊤ f)

  have ha' : f = algebraMap k Γ(Y, ⊤) a := by
    have := congrArg (Scheme.Modules.ofUnitSection ⊤) ha
    rw [Scheme.Modules.ofUnitSection_toUnitSection] at this
    rw [← this]
    show Scheme.Modules.ofUnitSection ⊤ ((algebraMap k Γ(Y, ⊤) a) • u₀) = _
    erw [Scheme.Modules.ofUnitSection_smul]
    rw [hu₀, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  by_cases ha0 : a = 0
  · left; rw [ha', ha0, map_zero]
  · right; rw [ha']; exact (Ne.isUnit ha0).map _

theorem zero_or_isUnit_of_finrank_H0_eq_one' {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (y : Y ⟶ Spec (.of k)) (𝒱 : Y.TwoAffineOpenCover)
    (h1 : Module.finrank k (𝒱.sectionsOf y (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).H0 = 1) :
    ∀ f : Γ(Y, ⊤), f = 0 ∨ IsUnit f := by
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  haveI : Nontrivial Γ(Y, ⊤) := inferInstance
  exact zero_or_isUnit_of_finrank_H0_eq_one y 𝒱 h1

theorem pullbackSection_eq_zero_iff_pullback_map_eq_zero {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (s : 𝟙_ X.Modules ⟶ M) :
    Scheme.Modules.pullbackSection F s = 0 ↔ (Scheme.Modules.pullback F).map s = 0 := by
  unfold Scheme.Modules.pullbackSection
  constructor
  · intro h
    have := congrArg (fun t => (Scheme.Modules.pullbackUnitIso F).hom ≫ t) h
    simp at this
    exact this
  · intro h
    erw [h]
    exact Limits.comp_zero

end FltWs21.M16G1
end G1

namespace M16

theorem finrank_H0_eq_and_finrank_H1_eq_of_equiv {k : Type u} [Field k]
    {𝒰 : TwoChartCech.Cover.{u} k} {𝒰' : TwoChartCech.Cover.{u} k}
    (S : TwoChartCech.Sections 𝒰) (S' : TwoChartCech.Sections 𝒰')
    (e₀ : S.M0 ≃ₗ[k] S'.M0) (e₁ : S.M1 ≃ₗ[k] S'.M1) (e₀₁ : S.M01 ≃ₗ[k] S'.M01)
    (h₀ : ∀ t, e₀₁ (S.r0 t) = S'.r0 (e₀ t)) (h₁ : ∀ t, e₀₁ (S.r1 t) = S'.r1 (e₁ t)) :
    Module.finrank k S.H0 = Module.finrank k S'.H0 ∧ Module.finrank k S.H1 = Module.finrank k S'.H1 := by

  have hd : ∀ p : S.M0 × S.M1, e₀₁ (S.cechDiff p) = S'.cechDiff (e₀.prodCongr e₁ p) := by
    rintro ⟨t₀, t₁⟩
    simp only [TwoChartCech.Sections.cechDiff_apply, map_sub, h₀, h₁, LinearEquiv.prodCongr_apply]
  constructor
  ·
    let f : S.H0 ≃ₗ[k] S'.H0 :=
      { toFun := fun p => ⟨e₀.prodCongr e₁ p.1, by
          have := p.2; rw [LinearMap.mem_ker] at this ⊢; rw [← hd, this, map_zero]⟩
        invFun := fun p => ⟨(e₀.prodCongr e₁).symm p.1, by
          have hp := p.2; rw [LinearMap.mem_ker] at hp ⊢
          apply e₀₁.injective; rw [hd, LinearEquiv.apply_symm_apply, hp, map_zero]⟩
        map_add' := fun p q => by ext <;> simp
        map_smul' := fun c p => by ext <;> simp
        left_inv := fun p => by ext <;> simp [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
        right_inv := fun p => by ext <;> simp [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply] }
    exact f.finrank_eq
  ·
    have hrange : (LinearMap.range S.cechDiff).map (e₀₁ : S.M01 →ₗ[k] S'.M01) = LinearMap.range S'.cechDiff := by
      ext y; constructor
      · rintro ⟨z, ⟨p, rfl⟩, rfl⟩; exact ⟨e₀.prodCongr e₁ p, (hd p).symm⟩
      · rintro ⟨p, rfl⟩
        refine ⟨S.cechDiff ((e₀.prodCongr e₁).symm p), ⟨_, rfl⟩, ?_⟩
        show e₀₁ (S.cechDiff ((e₀.prodCongr e₁).symm p)) = S'.cechDiff p
        rw [hd, LinearEquiv.apply_symm_apply]
    exact (Submodule.Quotient.equiv (LinearMap.range S.cechDiff) (LinearMap.range S'.cechDiff) e₀₁ hrange).finrank_eq

theorem numerics {k : Type u} [Field k] {s : ℕ} (hs : 0 < s) (a b : Fin s → kˣ) (ha : Function.Injective a)
    (g : ℕ)

    (n₀ m₀ : ℤ) (lam₀ : Fin s → kˣ) (h00 : n₀ = 0 ∧ m₀ = 0 ∧ ∀ i j, lam₀ i = lam₀ j)
    (hO1 : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam₀ n₀ m₀).H1 = g)

    (n m : ℤ) (lam : Fin s → kˣ) (hm : m = 0)
    (hM0 : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam n m).H0 = 1)
    (hM1 : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam n m).H1 = 0) :
    (s : ℤ) = g + 1 ∧ n = g := by
  obtain ⟨rfl, rfl, hlam⟩ := h00
  have hO0 : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam₀ 0 0).H0 = 1 :=
    ((TwoChartCech.finrank_H0_gluedLinesSections_zero_zero_le_one k hs a b lam₀).2).mpr hlam
  have h1 := (TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections k a b lam₀ ha 0 0).2.2
  have h2 := (TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections k a b lam ha n m).2.2
  rw [hO0, hO1] at h1
  rw [hM0, hM1] at h2
  subst hm
  constructor <;> omega

noncomputable def coverPreimage {X Y : Scheme.{u}} (𝒲 : X.TwoAffineOpenCover) (j : Y ⟶ X) [IsAffineHom j] :
    Y.TwoAffineOpenCover where
  U0 := j ⁻¹ᵁ 𝒲.U0
  U1 := j ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage j
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage j
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top, Scheme.Hom.preimage_top]
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage j

@[scoped simp] theorem coverPreimage_U0 {X Y : Scheme.{u}} (𝒲 : X.TwoAffineOpenCover) (j : Y ⟶ X) [IsAffineHom j] :
    (coverPreimage 𝒲 j).U0 = j ⁻¹ᵁ 𝒲.U0 := rfl
@[scoped simp] theorem coverPreimage_U1 {X Y : Scheme.{u}} (𝒲 : X.TwoAffineOpenCover) (j : Y ⟶ X) [IsAffineHom j] :
    (coverPreimage 𝒲 j).U1 = j ⁻¹ᵁ 𝒲.U1 := rfl

theorem support_zeroSchemeIdeal_zero {X : Scheme.{u}} (N : X.Modules) :
    ((Scheme.Modules.zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ N)).support : Set X) = Set.univ := by
  have h : Scheme.Modules.zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ N) = ⊥ := by
    apply le_bot_iff.mp
    apply Scheme.Modules.zeroSchemeIdeal_le
    intro U
    rw [Scheme.Modules.coeffIdeal, Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Scheme.IdealSheafData.ideal_bot, Ideal.mem_bot]
    have hz : ∀ (V : X.Opens) (m : Γ(𝟙_ X.Modules, V)), (0 : 𝟙_ X.Modules ⟶ N).app V m = 0 := fun V m => by
      rw [Scheme.Modules.Hom.zero_app]; rfl
    simp only [Scheme.Modules.coeff, Scheme.Modules.restrictSection, hz]
    show (U.1.topIso.hom (Scheme.Modules.ofUnitSection ⊤ (φ.app ⊤ 0))) ∈ ((⊥ : X.IdealSheafData).ideal U)
    rw [map_zero]
    show U.1.topIso.hom 0 ∈ _
    rw [map_zero]; exact Ideal.zero_mem _
  rw [h, Scheme.IdealSheafData.support_bot]; rfl

theorem step3 {k : Type u} [Field k] [IsAlgClosed k] (M₁ : AlgebraicCurve.CurveModel k (RatFunc k))
    {N : M₁.C.Modules} (hN : Scheme.Modules.IsInvertible N) (τ : 𝟙_ M₁.C.Modules ⟶ N) (hτ : τ ≠ 0)
    (g : ℕ) (𝒱₁ : M₁.C.TwoAffineOpenCover)
    (hχ : (Module.finrank k (𝒱₁.sectionsOf M₁.toBase N).H0 : ℤ) - Module.finrank k (𝒱₁.sectionsOf M₁.toBase N).H1 =
      (Module.finrank k (𝒱₁.sectionsOf M₁.toBase (𝟙_ M₁.C.Modules)).H0 : ℤ) -
        Module.finrank k (𝒱₁.sectionsOf M₁.toBase (𝟙_ M₁.C.Modules)).H1 + g)
    {s : ℕ} (p : Fin s → M₁.C) (hp : Function.Injective p)
    (hpz : ∀ i, p i ∈ (Scheme.Modules.zeroSchemeIdeal τ).support) (hsg : (s : ℤ) = g + 1) : False := by
  classical

  let Y' := pullback M₁.toBase (𝟙 (Spec (CommRingCat.of k)))
  let π : Y' ⟶ M₁.C := pullback.fst M₁.toBase (𝟙 _)
  haveI : IsIso π := inferInstance
  let φ : Y' ≅ M₁.C := asIso π
  have hφ : φ.hom ≫ M₁.toBase = pullback.snd M₁.toBase (𝟙 _) := by
    simp only [φ, asIso_hom, π]; rw [pullback.condition, Category.comp_id]
  let N' : Y'.Modules := (Scheme.Modules.pullback π).obj N
  have hN' : Scheme.Modules.IsInvertible N' := hN.pullback π
  let τ' : 𝟙_ Y'.Modules ⟶ N' := Scheme.Modules.pullbackSection π τ

  have hsupp' : ((Scheme.Modules.zeroSchemeIdeal τ').support : Set Y') = π.base ⁻¹' (Scheme.Modules.zeroSchemeIdeal τ).support := by
    rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal π hN τ, Scheme.IdealSheafData.support_comap]; rfl
  have hπφ : ∀ z, π.base (φ.inv.base z) = z := fun z => by
    show (φ.inv ≫ φ.hom).base z = z; rw [φ.inv_hom_id]; rfl

  haveI : GeometricallyIrreducible M₁.toBase := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed M₁.toBase
  have hτ' : τ' ≠ 0 := by
    intro h0
    have huniv : ((Scheme.Modules.zeroSchemeIdeal τ').support : Set Y') = Set.univ := by
      rw [h0]; exact support_zeroSchemeIdeal_zero N'
    apply Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal hN τ hτ
    have : φ.inv.base (genericPoint M₁.C) ∈ ((Scheme.Modules.zeroSchemeIdeal τ').support : Set Y') := by
      rw [huniv]; trivial
    rw [hsupp'] at this
    have h2 : π.base (φ.inv.base (genericPoint M₁.C)) ∈ ((Scheme.Modules.zeroSchemeIdeal τ).support : Set M₁.C) := this
    rwa [hπφ] at h2

  obtain ⟨𝒱, hU0, hU1, ⟨eH0⟩, ⟨eH1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd M₁.toBase (𝟙 _)) M₁.toBase φ hφ 𝒱₁ N N' (Iso.refl _)
  obtain ⟨𝒱u, hU0u, hU1u, ⟨uH0⟩, ⟨uH1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd M₁.toBase (𝟙 _)) M₁.toBase φ hφ 𝒱₁ (𝟙_ M₁.C.Modules) (𝟙_ Y'.Modules)
    ((Scheme.Modules.pullbackUnitIso φ.hom).symm)
  obtain rfl : 𝒱u = 𝒱 := by
    cases 𝒱u; cases 𝒱; simp only at hU0u hU1u hU0 hU1; subst hU0u; subst hU1u; cases hU0; cases hU1; rfl
  have hχ' : (Module.finrank k (𝒱u.sectionsOf (pullback.snd M₁.toBase (𝟙 _)) N').H0 : ℤ)
        - Module.finrank k (𝒱u.sectionsOf (pullback.snd M₁.toBase (𝟙 _)) N').H1
      = (Module.finrank k (𝒱u.sectionsOf (pullback.snd M₁.toBase (𝟙 _)) (𝟙_ Y'.Modules)).H0 : ℤ)
        - Module.finrank k (𝒱u.sectionsOf (pullback.snd M₁.toBase (𝟙 _)) (𝟙_ Y'.Modules)).H1 + g := by
    rw [eH0.finrank_eq, eH1.finrank_eq, uH0.finrank_eq, uH1.finrank_eq]; exact hχ

  obtain ⟨D, hDI, -⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (𝟙 (Spec (CommRingCat.of k))) hN' τ' hτ' 𝒱u g hχ'

  have hmem : ∀ i, φ.inv.base (p i) ∈ D.I.support := by
    intro i
    rw [hDI]
    show φ.inv.base (p i) ∈ ((Scheme.Modules.zeroSchemeIdeal τ').support : Set Y')
    rw [hsupp']
    show π.base (φ.inv.base (p i)) ∈ ((Scheme.Modules.zeroSchemeIdeal τ).support : Set M₁.C)
    rw [hπφ]; exact hpz i
  have hinj : Function.Injective fun i => φ.inv.base (p i) :=
    fun i j h => hp (φ.inv.homeomorph.injective h |> fun h' => by simpa using h')
  have hcard := RelEffCartierDiv.card_le_of_subset_support D (Finset.univ.image fun i => φ.inv.base (p i))
    (by simpa using fun i => hmem i)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  omega

end M16
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos.M16"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (U : C.Opens)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback c x)]

    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c x) (i₂ : M₂.C ⟶ pullback c x)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ pullback.snd c x = M₁.toBase) (hi₂ : i₂ ≫ pullback.snd c x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → kˣ) (hs : 0 < s) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : (pullback c x).TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)

    (hW₁ : ∃ W₁ : (pullback c x).Opens, (W₁ : Set ↥(pullback c x)) = (Set.range i₂.base)ᶜ ∧
      IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))

    (hU₁ : ∀ p : M₁.C, (∀ i, p ≠ (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
      (pullback.fst c x).base (i₁.base p) ∈ U)

    (g : ℕ)
    (hg : Module.finrank k (𝒲₀.sectionsOf (pullback.snd c x)
      (SheafOfModules.unit (pullback c x).ringCatSheaf)).H1 = g)

    (M : (pullback c x).Modules) (hMinv : Scheme.Modules.IsInvertible M)
    (hM₂ : Nonempty ((Scheme.Modules.pullback i₂).obj M ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback c x).ringCatSheaf)))
    (hM : Module.finrank k ↥(𝒲₀.sectionsOf (pullback.snd c x) M).H0 = 1 ∧
      Subsingleton (𝒲₀.sectionsOf (pullback.snd c x) M).H1)
    (σ : 𝟙_ (pullback c x).Modules ⟶ M) (hσ : σ ≠ 0) :
    ∃ Dx : RelEffCartierDiv c g x, Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U := by
  classical
  obtain ⟨W₁, hW₁c, hW₁imm⟩ := hW₁

  obtain ⟨n₀, m₀, lam₀, ⟨e₀, e₁, e₀₁, hr0, hr1⟩, hunit, -, -, -, -⟩ :=
    AlgebraicGeometry.TwoGluedProjectiveLines.exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
      k (pullback.snd c x) M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter htrans 𝒲₀ hU0₁ hU0₂ hU1₁ hU1₂
      (SheafOfModules.unit (pullback c x).ringCatSheaf) (Scheme.Modules.isInvertible_unit _)
  obtain ⟨n, m, lam, ⟨f₀, f₁, f₀₁, hf0, hf1⟩, -, -, hM2iff, hχ₁, -⟩ :=
    AlgebraicGeometry.TwoGluedProjectiveLines.exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
      k (pullback.snd c x) M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter htrans 𝒲₀ hU0₁ hU0₂ hU1₁ hU1₂ M hMinv
  have h00 := hunit.mp ⟨Iso.refl _⟩
  obtain ⟨hO0eq, hO1eq⟩ := M16.finrank_H0_eq_and_finrank_H1_eq_of_equiv _ _ e₀ e₁ e₀₁ hr0 hr1
  obtain ⟨hM0eq, hM1eq⟩ := M16.finrank_H0_eq_and_finrank_H1_eq_of_equiv _ _ f₀ f₁ f₀₁ hf0 hf1
  have hO1 : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam₀ n₀ m₀).H1 = g := hO1eq ▸ hg
  have hM0' : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam n m).H0 = 1 := hM0eq ▸ hM.1
  have hM1' : Module.finrank k (TwoChartCech.gluedLinesSections k a b lam n m).H1 = 0 := by
    rw [← hM1eq]; haveI := hM.2; exact Module.finrank_zero_of_subsingleton
  have hm : m = 0 := hM2iff.mp hM₂
  obtain ⟨hsg, hng⟩ := M16.numerics hs a b ha g n₀ m₀ lam₀ h00 hO1 n m lam hm hM0' hM1'

  haveI : IsAffineHom i₂ := inferInstance
  haveI : IsAffineHom i₁ := inferInstance
  have hΓ₂ := FltWs21.M16G1.zero_or_isUnit_of_finrank_H0_eq_one' M₂.toBase (M16.coverPreimage 𝒲₀ i₂)
    (AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₂ (M16.coverPreimage 𝒲₀ i₂)).2
  rcases FltWs21.M16G1.eq_zero_or_support_zeroSchemeIdeal_eq_empty (hMinv.pullback i₂)
      (hM₂.some ≪≫ Scheme.Modules.pullbackUnitIso i₂) hΓ₂ (Scheme.Modules.pullbackSection i₂ σ) with hz2 | hempty
  ·
    exfalso
    by_cases hz1 : Scheme.Modules.pullbackSection i₁ σ = 0
    · exact hσ (Scheme.Modules.IsInvertible.eq_zero_of_pullback_map_eq_zero_of_isReduced i₁ i₂ hcover hMinv σ
        ((FltWs21.M16G1.pullbackSection_eq_zero_iff_pullback_map_eq_zero i₁ σ).mp hz1)
        ((FltWs21.M16G1.pullbackSection_eq_zero_iff_pullback_map_eq_zero i₂ σ).mp hz2))
    ·
      let p : Fin s → M₁.C := fun i => (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1
      have hp : Function.Injective p := by
        intro i j h
        have h' := Subtype.ext_iff.mpr h
        have h'' := M₁.placeEquiv.symm.injective h'
        exact ha (Units.ext (RationalFunctionField.placeOfPoint_injective k h''))
      have hpz : ∀ i, p i ∈ (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i₁ σ)).support := by
        intro i
        have hq : (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1 ∈
            ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i₂ σ)).support : Set M₂.C) := by
          rw [hz2, M16.support_zeroSchemeIdeal_zero]; trivial
        rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i₂ hMinv σ, Scheme.IdealSheafData.support_comap] at hq
        have hX : i₁.base (p i) ∈ (Scheme.Modules.zeroSchemeIdeal σ).support := by rw [hnode i]; exact hq
        show p i ∈ ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i₁ σ)).support : Set M₁.C)
        rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i₁ hMinv σ, Scheme.IdealSheafData.support_comap]
        exact hX
      let 𝒱₁ := M16.coverPreimage 𝒲₀ i₁
      obtain ⟨h1O, h0O⟩ := AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₁ 𝒱₁
      exact M16.step3 M₁ (hMinv.pullback i₁) (Scheme.Modules.pullbackSection i₁ σ) hz1 g 𝒱₁
        (by rw [hχ₁ 𝒱₁, hng, Scheme.Modules.tensorUnit_eq, h1O, h0O]; ring) p hp hpz hsg
  ·
    have hdisj : ∀ q : M₂.C, i₂.base q ∉ (Scheme.Modules.zeroSchemeIdeal σ).support := by
      intro q hq
      have : q ∈ ((Scheme.Modules.zeroSchemeIdeal σ).comap i₂).support := by
        rw [Scheme.IdealSheafData.support_comap]; exact hq
      rw [Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i₂ hMinv σ] at this
      have h' : q ∈ (((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i₂ σ)).support : Set M₂.C)) := this
      rw [hempty] at h'; exact h'
    have hsupp : ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c x)) ⊆ (W₁ : Set ↥(pullback c x)) := by
      intro z hz; rw [hW₁c]; rintro ⟨q, rfl⟩; exact hdisj q hz
    have hW₁sub : (W₁ : Set ↥(pullback c x)) ⊆ Set.range i₁.base := by
      intro z hz; rw [hW₁c] at hz
      have := Set.eq_univ_iff_forall.mp hcover z
      rcases this with h | h
      · exact h
      · exact absurd h hz
    have hWU : W₁ ≤ (pullback.fst c x) ⁻¹ᵁ U := by
      intro z hz
      have hz' : z ∈ (W₁ : Set ↥(pullback c x)) := hz
      obtain ⟨p, rfl⟩ := hW₁sub hz'
      refine hU₁ p fun i hpi => ?_
      have hmem : i₁.base p ∈ Set.range i₂.base := ⟨_, (hpi ▸ hnode i).symm⟩
      rw [hW₁c] at hz'; exact hz' hmem

    have hσ1 : Scheme.Modules.pullbackSection i₁ σ ≠ 0 := by
      intro hz1
      let i0 : Fin s := ⟨0, hs⟩
      let p0 := (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i0 : k))).1
      have hp0 : p0 ∈ ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i₁ σ)).support : Set M₁.C) := by
        rw [hz1, M16.support_zeroSchemeIdeal_zero]; trivial
      have : i₁.base p0 ∈ (Scheme.Modules.zeroSchemeIdeal σ).support := by
        rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i₁ hMinv σ, Scheme.IdealSheafData.support_comap] at hp0
        exact hp0
      exact hdisj _ ((hnode i0) ▸ this)

    haveI : GeometricallyIrreducible M₁.toBase := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed M₁.toBase
    let 𝒱 := M16.coverPreimage 𝒲₀ i₁
    have hχ := hχ₁ 𝒱
    obtain ⟨h1O, h0O⟩ := AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₁ 𝒱
    haveI := hW₁imm
    obtain ⟨D, hDI, hDU⟩ :=
      AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion
        R c U k x M₁.toBase i₁ hi₁ W₁ hW₁sub hWU M hMinv σ hsupp hσ1 g 𝒱 (by
          rw [hχ, hng, Scheme.Modules.tensorUnit_eq, h1O, h0O]; ring)
    exact ⟨D, hDI, hDU⟩

end S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos (solution)
