-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e12d1c1e-213b-568a-9d6e-c3be970682c8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
import Theorems.Thm_AlgebraicCurve_finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc.AlgebraicGeometry.RelPicard AlgebraicCurve~genus NeronModelInfra"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth GeometricallyReduced SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral GeometricallyIrreducible Spec IsIntegral Spec.map Scheme Smooth smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr pullback_of_geometrically Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed GeometricallyReduced.of_isReduced_of_perfectField RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn RelPicard.IsAlgEquivZero.nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso RelPicard.exists_fibreIso_hom_comp_eq"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "fibreAt IsAlgEquivZero exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff fibreModule IsAlgEquivZero.nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero isAlgEquivZero_iff_eulerChar_sectionsOf_eq exists_fibreIso_hom_comp_eq"
namespace LineTrivDescent
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem finite_and_finrank_eq (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 𝒱' : X.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf x M).H0 ∧ Module.Finite K (𝒱.sectionsOf x M).H1 ∧
      Module.finrank K (𝒱.sectionsOf x M).H0 = Module.finrank K (𝒱'.sectionsOf x M).H0 ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = Module.finrank K (𝒱'.sectionsOf x M).H1 := by
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x M hM
  obtain ⟨hf0, hf1, h0, h1, -⟩ :=
    AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn 𝒱 x M D φ hnat hsmul hinj hrange
  obtain ⟨-, -, h0', h1', -⟩ :=
    AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn 𝒱' x M D φ hnat hsmul hinj hrange
  exact ⟨hf0, hf1, h0.trans h0'.symm, h1.trans h1'.symm⟩

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem nonempty_linearEquiv_H0_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[k] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[k] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem geometricallyIntegral_toBase (k : Type u) [Field k] [IsAlgClosed k] (M : CurveModel k (RatFunc k)) :
    GeometricallyIntegral M.toBase := by
  haveI : Smooth M.toBase := SmoothOfRelativeDimension.smooth (n := 1) (f := M.toBase)
  have h1 : GeometricallyReduced M.toBase :=
    AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField M.toBase
  have h2 : GeometricallyIrreducible M.toBase :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed M.toBase
  have := GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible
  have h : (@GeometricallyReduced ⊓ @GeometricallyIrreducible : MorphismProperty Scheme) M.toBase := ⟨h1, h2⟩
  rw [← this] at h
  exact h

theorem nonempty_pullback_iso_of_isAlgEquivZero_baseChange
    (k : Type u) [Field k] [IsAlgClosed k] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (M : CurveModel k (RatFunc k)) (𝒲M : M.C.TwoAffineOpenCover) (i : M.C ⟶ X) (hi : i ≫ x = M.toBase)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hΩ : IsAlgEquivZero (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
      ((Scheme.Modules.pullback (pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj L)) :
    Nonempty ((Scheme.Modules.pullback i).obj L ≅
      (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  classical
  set ι : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hι

  set N : M.C.Modules := (Scheme.Modules.pullback i).obj L with hN
  have hNinv : Scheme.Modules.IsInvertible N := hL.pullback i

  set Y : Scheme.{u} := Limits.pullback M.toBase ι with hY
  set y : Y ⟶ Spec (CommRingCat.of Ω) := pullback.snd M.toBase ι with hy
  set fM : Y ⟶ M.C := pullback.fst M.toBase ι with hfM
  set I : Y ⟶ Limits.pullback x ι := pullback.map M.toBase ι x ι i (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hi]) (by simp) with hIdef
  have hI : I ≫ pullback.snd x ι = y := by rw [hIdef, pullback.lift_snd, hy]; exact Category.comp_id _
  have hIfst : I ≫ pullback.fst x ι = fM ≫ i := by rw [hIdef, pullback.lift_fst, hfM]

  haveI : IsProper y := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 y := MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsIntegral Y :=
    pullback_of_geometrically (geometricallyIntegral_toBase k M).geometrically_isIntegral Ω ι

  have hIΩ : IsAlgEquivZero y ((Scheme.Modules.pullback I).obj
      ((Scheme.Modules.pullback (pullback.fst x ι)).obj L)) := hΩ.pullback I hI
  have eIN : (Scheme.Modules.pullback I).obj ((Scheme.Modules.pullback (pullback.fst x ι)).obj L) ≅
      (Scheme.Modules.pullback fM).obj N :=
    (Scheme.Modules.pullbackComp _ _).app L ≪≫ (Scheme.Modules.pullbackCongr hIfst).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm
  have hNΩ : IsAlgEquivZero y ((Scheme.Modules.pullback fM).obj N) := hIΩ.of_iso eIN

  set P1 := Limits.pullback M.toBase (𝟙 (Spec (CommRingCat.of k))) with hP1
  set Fs := Limits.pullback (pullback.snd M.toBase (𝟙 (Spec (CommRingCat.of k)))) (𝟙 (Spec (CommRingCat.of k))) with hFs
  set F' := Limits.pullback (pullback.snd M.toBase (𝟙 (Spec (CommRingCat.of k))))
    (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 (Spec (CommRingCat.of k))) with hF'

  obtain ⟨φ, hφsnd, hφfst, -⟩ := AlgebraicGeometry.RelPicard.exists_fibreIso_hom_comp_eq M.toBase (𝟙 _)
    (𝟙 (Spec (CommRingCat.of k))) (𝟙 _) (Category.id_comp _)
  let φ₁ : Fs ≅ M.C := φ ≪≫ asIso (pullback.fst M.toBase (𝟙 _))
  have hφ₁ : φ₁.hom ≫ M.toBase = fibreAt M.toBase (𝟙 _) (𝟙 _) := by
    show (φ.hom ≫ pullback.fst M.toBase (𝟙 _)) ≫ M.toBase = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hφsnd, Category.comp_id]
  have hφ₁' : pullback.fst (pullback.snd M.toBase (𝟙 _)) (𝟙 (Spec (CommRingCat.of k))) ≫
      pullback.fst M.toBase (𝟙 _) = φ₁.hom := hφfst.symm

  obtain ⟨φ₂, hφ₂snd, hφ₂fst, -⟩ := AlgebraicGeometry.RelPicard.exists_fibreIso_hom_comp_eq M.toBase (𝟙 _)
    (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 (Spec (CommRingCat.of k))) ι (by
      rw [Category.assoc, Category.comp_id]; rfl)
  have hφ₂' : pullback.fst (pullback.snd M.toBase (𝟙 _)) _ ≫ pullback.fst M.toBase (𝟙 _) = φ₂.hom ≫ fM :=
    hφ₂fst.symm

  have eU1 : fibreModule M.toBase (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) (SheafOfModules.unit P1.ringCatSheaf) ≅
      (Scheme.Modules.pullback φ₁.hom).obj (SheafOfModules.unit M.C.ringCatSheaf) :=
    Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm
  set N₁ : P1.Modules := (Scheme.Modules.pullback (pullback.fst M.toBase (𝟙 _))).obj N with hN₁
  have hN₁inv : Scheme.Modules.IsInvertible N₁ := hNinv.pullback _
  have eN1 : fibreModule M.toBase (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) N₁ ≅ (Scheme.Modules.pullback φ₁.hom).obj N :=
    (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr hφ₁').app N
  have eU2 : fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _)
      (SheafOfModules.unit P1.ringCatSheaf) ≅ (Scheme.Modules.pullback φ₂.hom).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm
  have eN2 : fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) N₁ ≅
      (Scheme.Modules.pullback φ₂.hom).obj ((Scheme.Modules.pullback fM).obj N) :=
    (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr hφ₂').app N ≪≫
      ((Scheme.Modules.pullbackComp _ _).app N).symm

  obtain ⟨𝒲s, hs0, hs1, ⟨eH0U⟩, ⟨eH1U⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt M.toBase (𝟙 _) (𝟙 _)) M.toBase φ₁ hφ₁ 𝒲M (SheafOfModules.unit M.C.ringCatSheaf) _ eU1
  obtain ⟨𝒲s', hs0', hs1', ⟨eH0N⟩, ⟨eH1N⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt M.toBase (𝟙 _) (𝟙 _)) M.toBase φ₁ hφ₁ 𝒲M N _ eN1
  obtain rfl : 𝒲s = 𝒲s' := cover_ext (hs0.trans hs0'.symm) (hs1.trans hs1'.symm)
  obtain ⟨hO1, hO0⟩ := AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M 𝒲M
  obtain ⟨hfinU0, hfinU1, -, -⟩ := finite_and_finrank_eq k M.toBase (SheafOfModules.unit M.C.ringCatSheaf)
    (Scheme.Modules.isInvertible_unit _) 𝒲M 𝒲M

  obtain ⟨𝒲', h0', h1'⟩ := AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
    M.toBase (𝟙 _) (SheafOfModules.unit P1.ringCatSheaf) (Scheme.Modules.isInvertible_unit _) (𝟙 _) 𝒲s Ω
  have hsub : Subsingleton (𝒲s.sectionsOf (fibreAt M.toBase (𝟙 _) (𝟙 _))
      (fibreModule M.toBase (𝟙 _) (𝟙 _) (SheafOfModules.unit P1.ringCatSheaf))).H1 := by
    haveI : Module.Finite k (𝒲s.sectionsOf (fibreAt M.toBase (𝟙 _) (𝟙 _))
      (fibreModule M.toBase (𝟙 _) (𝟙 _) (SheafOfModules.unit P1.ringCatSheaf))).H1 := Module.Finite.equiv eH1U.symm
    rw [← Module.finrank_zero_iff (R := k), eH1U.finrank_eq, hO1]
  have hsub' := h1'.mpr hsub
  have hφ₂y : φ₂.inv ≫ fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) = y := by
    rw [← hφ₂snd, Iso.inv_hom_id_assoc]
  obtain ⟨𝒲Y, -, -, -, ⟨eH1Y⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    y (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _)) φ₂.symm hφ₂y 𝒲'
    (fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) (SheafOfModules.unit P1.ringCatSheaf))
    (SheafOfModules.unit Y.ringCatSheaf)
    ((Scheme.Modules.pullbackUnitIso φ₂.inv).symm ≪≫
      (Scheme.Modules.pullback φ₂.inv).mapIso (Scheme.Modules.pullbackUnitIso _).symm)
  have h10Y : Module.finrank Ω (𝒲Y.sectionsOf y (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).H1 = 0 := by
    rw [eH1Y.finrank_eq]
    haveI := hsub'
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨eTriv⟩ := AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero
    Ω y ((Scheme.Modules.pullback fM).obj N) (hNinv.pullback fM) hNΩ y 𝒲Y h10Y (𝟙 Y) (Category.id_comp _)
  have eNΩ : (Scheme.Modules.pullback fM).obj N ≅ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) :=
    ((Scheme.Modules.pullbackId Y).app _).symm ≪≫ eTriv

  have step8 : Module.finrank k (𝒲M.sectionsOf M.toBase N).H0 = 1 ∧
      Module.finrank k (𝒲M.sectionsOf M.toBase N).H1 = 0 := by

    have hF'eq : fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) = φ₂.hom ≫ y := hφ₂snd.symm
    haveI : IsIntegral F' := IsIntegral.of_isIso φ₂.inv
    haveI : IsProper (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _)) := by
      rw [hF'eq]; infer_instance
    haveI : SmoothOfRelativeDimension 1 (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _)) := by
      rw [hF'eq]
      exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) φ₂.hom y).mpr inferInstance

    obtain ⟨𝒲'N, h0N', h1N'⟩ := AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
      M.toBase (𝟙 _) N₁ hN₁inv (𝟙 _) 𝒲s Ω

    have eTrivF' : fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) N₁ ≅
        (SheafOfModules.unit F'.ringCatSheaf : F'.Modules) :=
      eN2 ≪≫ (Scheme.Modules.pullback φ₂.hom).mapIso eNΩ ≪≫ Scheme.Modules.pullbackUnitIso φ₂.hom
    obtain ⟨hcN0, hcN1⟩ := finrank_H0_H1_congr (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
      𝒲'N eTrivF'
    obtain ⟨⟨lcN0⟩, ⟨lcN1⟩⟩ := nonempty_linearEquiv_H0_H1_congr
      (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _)) 𝒲'N eTrivF'

    obtain ⟨hfU0', hfU1', hU0eq, hU1eq⟩ := finite_and_finrank_eq Ω
      (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
      (SheafOfModules.unit F'.ringCatSheaf) (Scheme.Modules.isInvertible_unit _) 𝒲'N 𝒲'
    obtain ⟨hcU0, hcU1⟩ := finrank_H0_H1_congr (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
      𝒲' (Scheme.Modules.pullbackUnitIso
        (pullback.fst (pullback.snd M.toBase (𝟙 _)) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _)) :
        fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) (SheafOfModules.unit P1.ringCatSheaf) ≅ _)
    have hU0one : Module.finrank Ω (𝒲'.sectionsOf (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
        (SheafOfModules.unit F'.ringCatSheaf : F'.Modules)).H0 = 1 := by
      rw [← hcU0, h0', eH0U.finrank_eq, hO0]
    have hU1zero : Module.finrank Ω (𝒲'.sectionsOf (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
        (SheafOfModules.unit F'.ringCatSheaf : F'.Modules)).H1 = 0 := by
      rw [← hcU1]
      haveI := hsub'
      exact Module.finrank_zero_of_subsingleton

    have hN'0 : Module.finrank Ω (𝒲'N.sectionsOf (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
        (fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) N₁)).H0 = 1 := by
      rw [hcN0, hU0eq, hU0one]
    have hN'1 : Subsingleton (𝒲'N.sectionsOf (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
        (fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) N₁)).H1 := by
      haveI : Module.Finite Ω (𝒲'N.sectionsOf (fibreAt M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _))
        (fibreModule M.toBase (𝟙 _) (Scheme.TwoAffineOpenCover.specMap k Ω ≫ 𝟙 _) N₁)).H1 :=
        Module.Finite.equiv lcN1.symm
      rw [← Module.finrank_zero_iff (R := Ω), hcN1, hU1eq, hU1zero]

    have hs1 : Subsingleton (𝒲M.sectionsOf M.toBase N).H1 :=
      (eH1N.toEquiv.subsingleton_congr).mp (h1N'.mp hN'1)
    refine ⟨?_, ?_⟩
    · rw [← eH0N.finrank_eq, ← h0N', hN'0]
    · haveI := hs1; exact Module.finrank_zero_of_subsingleton

  obtain ⟨hO1, hO0⟩ := AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M 𝒲M
  have hN0 : IsAlgEquivZero M.toBase N := by
    rw [AlgebraicGeometry.RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq k M.toBase N hNinv 𝒲M,
      step8.1, step8.2, hO0, hO1]
  obtain ⟨eN⟩ := AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero
    k M.toBase N hNinv hN0 M.toBase 𝒲M hO1 (𝟙 M.C) (Category.id_comp _)
  exact ⟨((Scheme.Modules.pullbackId M.C).app N).symm ≪≫ eN ≪≫ (Scheme.Modules.pullbackUnitIso i).symm⟩

end AlgebraicGeometry.RelPicard.LineTrivDescent

end

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (M : CurveModel k (RatFunc k)) (𝒲M : M.C.TwoAffineOpenCover) (i : M.C ⟶ X) (hi : i ≫ x = M.toBase)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hΩ : IsAlgEquivZero (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
      ((Scheme.Modules.pullback (pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj L)) :
    Nonempty ((Scheme.Modules.pullback i).obj L ≅
      (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  AlgebraicGeometry.RelPicard.LineTrivDescent.nonempty_pullback_iso_of_isAlgEquivZero_baseChange k Ω x M 𝒲M i hi L hL hΩ

end S_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc (solution)
