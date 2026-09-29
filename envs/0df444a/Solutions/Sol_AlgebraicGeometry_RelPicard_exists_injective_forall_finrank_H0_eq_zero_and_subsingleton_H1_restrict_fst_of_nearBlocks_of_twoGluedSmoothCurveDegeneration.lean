-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c545e00f-52e7-5c3e-a404-e66eb39090d2

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom GeometricallyIntegral Scheme.Pullback.range_fst Spec IsIntegral Spec.map Scheme pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackId Scheme.Modules pullbackRestrictIsoRestrict Scheme.Opens IsIntegral.of_isIso IsOpenImmersion.lift_fac Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover SmoothProperCurve.specMap Scheme.IdealSheafData.isInvertible_top TwoGluedCurves.nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace N1NearBlocks
p2m_open "AlgebraicGeometry"

variable {A : Type u} [CommRing A] {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of A))
  {M : ℕ} {B : Fin M → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  {deg : Fin M → ℕ}
  (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C') (hz : ∀ i, z i ≫ c' = specMap A (B i))
  {Ω : Type u} [Field Ω] [Algebra A Ω]

def ptOf (i : Fin M) (ψ : B i →ₐ[A] Ω) :
    {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z i) (𝟙 _) (by
      rw [Category.assoc, hz i, Category.id_comp]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem ptOf_fst (i : Fin M) (ψ : B i →ₐ[A] Ω) :
    (ptOf c' z hz i ψ).1 ≫ pullback.fst c' (specMap A Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z i :=
  pullback.lift_fst _ _ _

variable [∀ i, Fintype (B i →ₐ[A] Ω)]

def blockAll (i : Fin M) :
    Finset {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} := by
  classical
  exact Finset.univ.image (ptOf c' z hz i)

theorem ptOf_mem_blockAll (i : Fin M) (ψ : B i →ₐ[A] Ω) : ptOf c' z hz i ψ ∈ blockAll c' z hz i := by
  classical
  unfold blockAll
  exact Finset.mem_image_of_mem _ (Finset.mem_univ ψ)

theorem card_blockAll_le (hcnt : ∀ i, Fintype.card (B i →ₐ[A] Ω) ≤ deg i) (i : Fin M) :
    (blockAll c' z hz (Ω := Ω) i).card ≤ deg i := by
  classical
  unfold blockAll
  exact Finset.card_image_le.trans (by rw [Finset.card_univ]; exact hcnt i)

theorem blockAll_nonempty (i : Fin M) (h : Nonempty (B i →ₐ[A] Ω)) : (blockAll c' z hz (Ω := Ω) i).Nonempty :=
  ⟨_, ptOf_mem_blockAll c' z hz i h.some⟩

theorem mem_blockAll_iff (i : Fin M)
    (q : {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _}) :
    q ∈ blockAll c' z hz i ↔ ∃ ψ, ptOf c' z hz i ψ = q := by
  classical
  unfold blockAll
  simp

theorem range_subset_of_mem_blockAll (i : Fin M)
    (q : {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _})
    (hq : q ∈ blockAll c' z hz i) :
    Set.range (q.1 ≫ pullback.fst c' (specMap A Ω)).base ⊆ Set.range (z i).base := by
  obtain ⟨ψ, rfl⟩ := (mem_blockAll_iff c' z hz i q).mp hq
  rw [ptOf_fst]
  rintro _ ⟨y, rfl⟩
  exact ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base y, rfl⟩

theorem disjoint_blockAll (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    {i j : Fin M} (hij : i ≠ j) : Disjoint (blockAll c' z hz (Ω := Ω) i) (blockAll c' z hz j) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqi hqj
  have hi := range_subset_of_mem_blockAll c' z hz i q hqi
  have hj := range_subset_of_mem_blockAll c' z hz j q hqj
  have hpt : (q.1 ≫ pullback.fst c' (specMap A Ω)).base (IsLocalRing.closedPoint Ω) ∈
      Set.range (z i).base ∩ Set.range (z j).base := ⟨hi ⟨_, rfl⟩, hj ⟨_, rfl⟩⟩
  exact Set.disjoint_iff.mp (hdisj hij) hpt

end AlgebraicGeometry.N1NearBlocks
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.N1NearBlocks"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom GeometricallyIntegral Scheme.Pullback.range_fst Spec IsIntegral Spec.map Scheme pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackId Scheme.Modules pullbackRestrictIsoRestrict Scheme.Opens IsIntegral.of_isIso IsOpenImmersion.lift_fac Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover SmoothProperCurve.specMap Scheme.IdealSheafData.isInvertible_top TwoGluedCurves.nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace N1NearImpl
p2m_open "AlgebraicGeometry"

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem H0H1_equiv_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[k] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[k] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem smoothOfRelativeDimension_one_preimage_ι_comp_snd {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of R)) :
    SmoothOfRelativeDimension 1 ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have h : (pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s =
      (pullbackRestrictIsoRestrict (pullback.fst c s) U).inv ≫ (pullbackSymmetry (pullback.fst c s) U.ι).hom ≫
        (pullbackRightPullbackFstIso c s U.ι).hom ≫ pullback.snd (U.ι ≫ c) s := by
    rw [pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackRestrictIsoRestrict_inv_fst_assoc]
  rw [h, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1),
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1),
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)]
  infer_instance

theorem isInvertible_ker_of_mem {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
    (p : Spec (CommRingCat.of Ω) ⟶ pullback c s) (hp : p ≫ pullback.snd c s = 𝟙 _)
    (hpU : Set.range p.base ⊆ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))) :
    p.ker.IsInvertible := by
  haveI : IsSeparated (pullback.snd c s) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI := smoothOfRelativeDimension_one_preimage_ι_comp_snd c U s
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens (pullback.snd c s) (pullback.fst c s ⁻¹ᵁ U) p hp
    (hpU ⟨_, rfl⟩)

end AlgebraicGeometry.N1NearImpl
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.N1NearBlocks"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.N1NearBlocks"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.N1NearBlocks"

open AlgebraicGeometry.N1NearBlocks AlgebraicGeometry.N1NearImpl in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) {b : ℕ} (hb : 1 ≤ b) (hdegb : ∀ i, deg i ≤ b)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i))

    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of Ω)) (c₂ : C₂ ⟶ Spec (CommRingCat.of Ω))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (pullback.snd c (SmoothProperCurve.specMap R Ω))) (i₂ : SchemeHomOver c₂ (pullback.snd c (SmoothProperCurve.specMap R Ω)))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1] (n : ℕ)
    (hbadΩ :
        (∀ z : ↥(pullback c (SmoothProperCurve.specMap R Ω)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) =
          connectedComponentIn ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
            (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) =
          ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \
            connectedComponentIn ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
              (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) ∧
        (∃ W₁ : (pullback c (SmoothProperCurve.specMap R Ω)).Opens, (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c (SmoothProperCurve.specMap R Ω)).Opens, (W₂ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))

    (hzε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base ⊆
      connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (r γ₁ e₁ : ℕ) (𝒱₁ : C₁.TwoAffineOpenCover)
    (hγ₁ : Module.finrank Ω (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf)).H1 = γ₁)
    (he₁ : γ₁ + n + e₁ = r + 1) (hr₁ : 2 * γ₁ + n ≤ r + 1)
    (hcount₁ : r * b ^ e₁ + e₁ < M)

    (r' : ℕ) {d : ℕ} (q : Fin d → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
    (hq₁ : ∀ m, Set.range (q m).1.base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₁.1.base)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a : Fin e₁ → Fin M, Function.Injective a ∧
      ∀ (v : Fin e₁ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        ∀ {e₂ : ℕ} (v' : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, Set.range (v' j).1.base ⊆
            (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₁.1.base) →
          ∀ 𝒲₁ : C₁.TwoAffineOpenCover,
            Module.finrank Ω (𝒲₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗
                ((pullback.fst i₁.1 i₂.1).ker).module)).H0 = 0 ∧
            Subsingleton (𝒲₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗
                ((pullback.fst i₁.1 i₂.1).ker).module)).H1 := by
  classical
  have hbadΩ' := hbadΩ
  obtain ⟨hcov, hcr, hn, hn0, hεpl, hUtr, hC₁U, hC₂U, ⟨W₁, hW₁, hoi⟩, -⟩ := hbadΩ'
  haveI := hoi
  haveI : IsIntegral C₁ :=
    haveI : IsIntegral (pullback c₁ (𝟙 (Spec (CommRingCat.of Ω)))) := inferInstance
    IsIntegral.of_isIso (pullback.fst c₁ (𝟙 (Spec (CommRingCat.of Ω))))
  haveI : ∀ i, Fintype (B i →ₐ[R] Ω) := fun i => Fintype.ofEquiv _ (eB i).symm

  have hN : Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base = Set.range i₁.1.base ∩ Set.range i₂.1.base := by
    rw [show (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base = (pullback.fst i₁.1 i₂.1).base ≫ i₁.1.base from rfl,
      TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst, Set.image_preimage_eq_range_inter]
  have hgood : ∀ y : ↥(pullback c (SmoothProperCurve.specMap R Ω)), y ∈ Set.range i₁.1.base ∩ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) →
      y ∈ Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ := by
    rintro y ⟨hy₁, hyU⟩
    refine ⟨hy₁, fun hy₂ => ?_⟩
    rw [hUtr, hN] at hyU
    exact hyU ⟨hy₁, hy₂⟩
  have hrangej : Set.range ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1).base = Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ := by
    rw [show ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1).base = (i₁.1 ⁻¹ᵁ W₁).ι.base ≫ i₁.1.base from rfl,
      TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, ← hW₁]
    exact Set.image_preimage_eq_range_inter

  have liftEx : ∀ (p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω)),
      Set.range p.base ⊆ Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ →
      ∃ p₁ : Spec (CommRingCat.of Ω) ⟶ C₁, p₁ ≫ i₁.1 = p := fun p hp =>
    ⟨IsOpenImmersion.lift ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1) p (by rwa [hrangej]) ≫ (i₁.1 ⁻¹ᵁ W₁).ι, by
      rw [Category.assoc, IsOpenImmersion.lift_fac]⟩
  have over_of_fac : ∀ (p₁ : Spec (CommRingCat.of Ω) ⟶ C₁) (p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
      p₁ ≫ i₁.1 = p.1 → p₁ ≫ c₁ = 𝟙 _ := fun p₁ p hfac =>
    calc p₁ ≫ c₁ = p₁ ≫ (i₁.1 ≫ pullback.snd c (SmoothProperCurve.specMap R Ω)) := by rw [i₁.2]
      _ = (p₁ ≫ i₁.1) ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) := (Category.assoc _ _ _).symm
      _ = p.1 ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) := by rw [hfac]
      _ = 𝟙 _ := p.2
  have hε₀good : Set.range (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.base ⊆
      Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ := by
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    exact ⟨hεpl.1, hεpl.2⟩
  obtain ⟨ε₁', hε₁'⟩ := liftEx _ hε₀good
  let ε₁ : {p : Spec (CommRingCat.of Ω) ⟶ C₁ //
          p ≫ c₁ = 𝟙 _} :=
    ⟨ε₁', over_of_fac ε₁' (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)) hε₁'⟩
  let liftOr : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _} → {p : Spec (CommRingCat.of Ω) ⟶ C₁ //
          p ≫ c₁ = 𝟙 _} := fun p =>
    if h : Set.range p.1.base ⊆ Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ then
      ⟨(liftEx p.1 h).choose, over_of_fac _ p (liftEx p.1 h).choose_spec⟩
    else ε₁
  have liftOr_fac : ∀ p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
      Set.range p.1.base ⊆ Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ → (liftOr p).1 ≫ i₁.1 = p.1 := by
    intro p h
    simp only [liftOr, dif_pos h]
    exact (liftEx p.1 h).choose_spec

  have hblk : ∀ (i : Fin M) (p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
      p ∈ blockAll c z hz i →
      Set.range p.1.base ⊆ Set.range i₁.1.base ∩ (Set.range i₂.1.base)ᶜ ∧
        Set.range p.1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    intro i p hp
    have hsub := range_subset_of_mem_blockAll c z hz i p hp
    have h2 : ∀ t, p.1.base t ∈ Set.range i₁.1.base ∩ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := fun t => by
      rw [hC₁U]
      exact hzε i (show (p.1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω)).base t ∈ Set.range (z i).base from hsub ⟨t, rfl⟩)
    exact ⟨by rintro _ ⟨t, rfl⟩; exact hgood _ (h2 t), by rintro _ ⟨t, rfl⟩; exact (h2 t).2⟩

  let B₁ : Fin M → Finset {p : Spec (CommRingCat.of Ω) ⟶ C₁ //
          p ≫ c₁ = 𝟙 _} :=
    fun i => (blockAll c z hz i).image liftOr
  have hB₁disj : ∀ i i', i ≠ i' → Disjoint (B₁ i) (B₁ i') := by
    intro i i' hii'
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p', hp', hpp'⟩ := Finset.mem_image.mp hq'
    have h1 := liftOr_fac p (hblk i p hp).1
    have h2 := liftOr_fac p' (hblk i' p' hp').1
    have : p' = p := Subtype.ext (by rw [← h1, ← h2, hpp'])
    subst this
    exact Finset.disjoint_left.mp (disjoint_blockAll c z hz hzdisj hii') hp hp'
  have hB₁card : ∀ i, (B₁ i).card ≤ b := fun i =>
    Finset.card_image_le.trans ((card_blockAll_le c z hz
      (fun i => le_of_eq (by rw [Fintype.card_congr (eB i), Fintype.card_fin])) i).trans (hdegb i))

  obtain ⟨N₁, hN₁card, hN₁prod, -, -⟩ :=
    AlgebraicGeometry.TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced Ω
      (pullback.snd c (SmoothProperCurve.specMap R Ω)) c₁ c₂ i₁ i₂ hcr n hn hn0

  obtain ⟨a, ha, hgen⟩ :=
    AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
      Ω c₁ γ₁ 𝒱₁ hγ₁ ((Scheme.Modules.pullback i₁.1).obj L₀) (hL₀.pullback _) (h0.pullback i₁.1 i₁.2)
      (fun _ : Fin r => ε₁) (fun _ : Fin 1 => N₁) e₁
      (fun _ => by rw [hN₁card]; omega) (fun _ => by rw [hN₁card]; omega)
      B₁ hB₁disj hb hB₁card (show 1 * r * b ^ e₁ + e₁ < Fintype.card (Fin M) by rw [Fintype.card_fin]; simpa using hcount₁)
  refine ⟨a, ha, ?_⟩
  intro v hv e₂ v' hv' 𝒲₁

  have hvblk : ∀ j, v j ∈ blockAll c z hz (a j) := fun j => by
    obtain ⟨ψ, hψ⟩ := hv j
    rw [mem_blockAll_iff]
    refine ⟨ψ, Subtype.ext (pullback.hom_ext ?_ ?_)⟩
    · rw [ptOf_fst, hψ]
    · rw [(ptOf c z hz (a j) ψ).2, (v j).2]
  have hv₁mem : ∀ j, liftOr (v j) ∈ B₁ (a j) := fun j => Finset.mem_image_of_mem _ (hvblk j)
  have hv₁fac : ∀ j, (liftOr (v j)).1 ≫ i₁.1 = (v j).1 := fun j => liftOr_fac (v j) (hblk _ _ (hvblk j)).1
  obtain ⟨hH0, hH1⟩ := hgen (fun j => liftOr (v j)) hv₁mem 0 𝒲₁

  haveI : IsSeparated c := inferInstance
  have hker : ∀ p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}, Set.range p.1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) → p.1.ker.IsInvertible :=
    fun p hp => isInvertible_ker_of_mem c U (SmoothProperCurve.specMap R Ω) p.1 p.2 hp
  have hεtr : Set.range (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    rintro _ ⟨t, rfl⟩
    show ((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω)).base t ∈ (U : Set C)
    rw [show (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = (SmoothProperCurve.specMap R Ω) ≫ ε.1 from pullback.lift_fst _ _ _]
    exact hεU ⟨_, rfl⟩
  obtain ⟨eK5⟩ :=
    AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible Ω (pullback.snd c (SmoothProperCurve.specMap R Ω))
      c₁ c₂ i₁ i₂ W₁ hW₁ hoi L₀ hL₀ r (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)) (fun y hy => (hε₀good hy).2) (hker _ hεtr)
      ε₁ hε₁' v (fun j y hy => ((hblk _ _ (hvblk j)).1 hy).2) (fun j => hker _ (hblk _ _ (hvblk j)).2)
      (fun j => liftOr (v j)) hv₁fac
      r' q (fun m y hy => (hq₁ m hy).2) (fun m => hker _ (fun y hy => (hq₁ m hy).1))
      v' (fun j y hy => (hv' j hy).2) (fun j => hker _ (fun y hy => (hv' j hy).1))
      (by
        haveI : IsSeparated c₁ := inferInstance
        rw [← hN₁prod]
        exact Finset.prod_induction _ (fun I : C₁.IdealSheafData => I.IsInvertible)
          (fun _ _ h h' => h.mul h') Scheme.IdealSheafData.isInvertible_top
          (fun p _ => Scheme.Hom.isInvertible_ker_of_comp_eq_id p.1 p.2))
  have e' : _ ≅ (Scheme.Modules.pullback i₁.1).obj L₀ ⊗
      ((∏ _l : Fin r, ε₁.1.ker).invModule ⊗ ((∏ j, (liftOr (v j)).1.ker) * ∏ p ∈ N₁, p.1.ker).module) :=
    eK5 ≪≫ eqToIso (by rw [hN₁prod])
  obtain ⟨⟨f0⟩, ⟨f1⟩⟩ := H0H1_equiv_of_iso c₁ 𝒲₁ e'
  refine ⟨?_, ?_⟩
  · rw [f0.finrank_eq]
    rw [hN₁card] at hH0
    omega
  · haveI := hH1
    exact f1.toEquiv.subsingleton

end S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration (solution)
