-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ee269334-5240-5f13-b67b-8933c6c6870e

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
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply"
p2m_attr_erase "simp" "ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral QuasiCompact Scheme.preimage_basicOpen LocallyOfFiniteType GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Spec.map Scheme pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange eq_zero_of_basicOpen_eq_bot IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Modules.pullbackId Scheme.Modules pullbackRestrictIsoRestrict Scheme.Hom.ker_apply Scheme.IdealSheafData.le_def Scheme.IdealSheafData isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover SmoothProperCurve.specMap Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.exists_tensor_iso_mul_module Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card TwoGluedCurves.nonempty_pullback_chartModule_iso_snd"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "IsAlgEquivZero sectionFibrePoint exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card"
namespace K3Far
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

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

section S1

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  {C₂ : Scheme.{u}} {c₂ : C₂ ⟶ Spec (CommRingCat.of Ω)}
  (i₂ : SchemeHomOver c₂ (pullback.snd c (specMap R Ω))) [IsClosedImmersion i₂.1]

theorem subset_range_diff_of_subset_diff {X : Type*} {r₁ r₂ Utr cc S : Set X}
    (h7 : r₁ ∩ Utr = cc) (h8 : r₂ ∩ Utr = Utr \ cc) (hS : S ⊆ Utr \ cc) : S ⊆ r₂ \ r₁ := by
  intro z hz
  have hz' := hS hz
  refine ⟨?_, fun h1 => hz'.2 ?_⟩
  · have : z ∈ r₂ ∩ Utr := by rw [h8]; exact hz'
    exact this.1
  · rw [← h7]; exact ⟨h1, hz'.1⟩

def liftSnd (s : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hs : Set.range s.1.base ⊆ Set.range i₂.1.base) :
    {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} :=
  ⟨(IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i₂.1 s.1 hs).choose, by
    have h := (IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i₂.1 s.1 hs).choose_spec.1
    have e : (IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i₂.1 s.1 hs).choose ≫ c₂ =
        ((IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i₂.1 s.1 hs).choose ≫ i₂.1) ≫
          pullback.snd c (specMap R Ω) := by
      rw [Category.assoc, i₂.2]
    rw [e, h, s.2]⟩

theorem liftSnd_comp (s : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hs : Set.range s.1.base ⊆ Set.range i₂.1.base) : (liftSnd c i₂ s hs).1 ≫ i₂.1 = s.1 :=
  (IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i₂.1 s.1 hs).choose_spec.1

theorem eq_liftSnd (s : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hs : Set.range s.1.base ⊆ Set.range i₂.1.base) (p : {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _})
    (hp : p.1 ≫ i₂.1 = s.1) : p = liftSnd c i₂ s hs :=
  Subtype.ext ((cancel_mono i₂.1).mp (hp.trans (liftSnd_comp c i₂ s hs).symm))

theorem eq_of_liftSnd_eq
    (s s' : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hs : Set.range s.1.base ⊆ Set.range i₂.1.base) (hs' : Set.range s'.1.base ⊆ Set.range i₂.1.base)
    (h : liftSnd c i₂ s hs = liftSnd c i₂ s' hs') : s = s' :=
  Subtype.ext (by rw [← liftSnd_comp c i₂ s hs, ← liftSnd_comp c i₂ s' hs', h])

theorem range_liftSnd_comp
    (s : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hs : Set.range s.1.base ⊆ Set.range i₂.1.base) :
    Set.range ((liftSnd c i₂ s hs).1 ≫ i₂.1).base = Set.range s.1.base := by
  rw [liftSnd_comp]

theorem range_subset_W₂ {X : Scheme.{u}} {S r₁ r₂ : Set X} (W₂ : X.Opens) (hW₂ : (W₂ : Set X) = r₁ᶜ)
    (hS : S ⊆ r₂ \ r₁) : S ⊆ W₂ := by
  intro z hz
  have : z ∈ (W₂ : Set X) := by rw [hW₂]; exact (hS hz).2
  exact this

end S1

section S2

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {M' : ℕ} {B' : Fin M' → Type u} [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
  (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
  (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  {C₂ : Scheme.{u}} {c₂ : C₂ ⟶ Spec (CommRingCat.of Ω)}
  (i₂ : SchemeHomOver c₂ (pullback.snd c (specMap R Ω))) [IsClosedImmersion i₂.1]

def ptOf (i : Fin M') (ψ : B' i →ₐ[R] Ω) :
    {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _} :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i) (𝟙 _) (by
      rw [Category.assoc, hz' i, Category.id_comp]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem ptOf_fst (i : Fin M') (ψ : B' i →ₐ[R] Ω) :
    (ptOf c z' hz' i ψ).1 ≫ pullback.fst c (specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i :=
  pullback.lift_fst _ _ _

theorem range_ptOf_subset (i : Fin M') (ψ : B' i →ₐ[R] Ω) :
    Set.range (ptOf c z' hz' i ψ).1.base ⊆ (pullback.fst c (specMap R Ω)).base ⁻¹' Set.range (z' i).base := by
  rintro _ ⟨t, rfl⟩
  show (((ptOf c z' hz' i ψ).1 ≫ pullback.fst c (specMap R Ω)).base t) ∈ Set.range (z' i).base
  rw [ptOf_fst]
  exact ⟨_, rfl⟩

theorem eq_ptOf_of_fst_eq (i : Fin M') (ψ : B' i →ₐ[R] Ω)
    (v : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hv : v.1 ≫ pullback.fst c (specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i) :
    v = ptOf c z' hz' i ψ :=
  Subtype.ext (pullback.hom_ext (by rw [hv, ptOf_fst]) (by rw [v.2, (ptOf c z' hz' i ψ).2]))

variable (hon : ∀ (i : Fin M') (ψ : B' i →ₐ[R] Ω), Set.range (ptOf c z' hz' i ψ).1.base ⊆ Set.range i₂.1.base)

def blk [∀ i, Fintype (B' i →ₐ[R] Ω)] (i : Fin M') : Finset {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} := by
  classical
  exact Finset.univ.image fun ψ => liftSnd c i₂ (ptOf c z' hz' i ψ) (hon i ψ)

theorem card_blk_le [∀ i, Fintype (B' i →ₐ[R] Ω)] (i : Fin M') :
    (blk c z' hz' i₂ hon i).card ≤ Fintype.card (B' i →ₐ[R] Ω) := by
  classical
  unfold blk
  exact Finset.card_image_le.trans (by rw [Finset.card_univ])

theorem mem_blk_iff [∀ i, Fintype (B' i →ₐ[R] Ω)] (i : Fin M') (p : {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) :
    p ∈ blk c z' hz' i₂ hon i ↔ ∃ ψ, liftSnd c i₂ (ptOf c z' hz' i ψ) (hon i ψ) = p := by
  classical
  unfold blk
  simp

theorem range_subset_of_mem_blk [∀ i, Fintype (B' i →ₐ[R] Ω)] (i : Fin M')
    (p : {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) (hp : p ∈ blk c z' hz' i₂ hon i) :
    Set.range (p.1 ≫ i₂.1 ≫ pullback.fst c (specMap R Ω)).base ⊆ Set.range (z' i).base := by
  obtain ⟨ψ, rfl⟩ := (mem_blk_iff c z' hz' i₂ hon i p).mp hp
  rw [← Category.assoc, liftSnd_comp, ptOf_fst]
  rintro _ ⟨y, rfl⟩
  exact ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base y, rfl⟩

theorem disjoint_blk [∀ i, Fintype (B' i →ₐ[R] Ω)]
    (hdisj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    {i j : Fin M'} (hij : i ≠ j) : Disjoint (blk c z' hz' i₂ hon i) (blk c z' hz' i₂ hon j) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi := range_subset_of_mem_blk c z' hz' i₂ hon i p hpi
  have hj := range_subset_of_mem_blk c z' hz' i₂ hon j p hpj
  have hpt : (p.1 ≫ i₂.1 ≫ pullback.fst c (specMap R Ω)).base (IsLocalRing.closedPoint Ω) ∈
      Set.range (z' i).base ∩ Set.range (z' j).base := ⟨hi ⟨_, rfl⟩, hj ⟨_, rfl⟩⟩
  exact Set.disjoint_iff.mp (hdisj hij) hpt

theorem liftSnd_mem_blk [∀ i, Fintype (B' i →ₐ[R] Ω)] (i : Fin M') (ψ : B' i →ₐ[R] Ω)
    (v : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hv : v.1 ≫ pullback.fst c (specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i)
    (hvon : Set.range v.1.base ⊆ Set.range i₂.1.base) :
    liftSnd c i₂ v hvon ∈ blk c z' hz' i₂ hon i := by
  have e := eq_ptOf_of_fst_eq c z' hz' i ψ v hv
  subst e
  exact (mem_blk_iff c z' hz' i₂ hon i _).mpr ⟨ψ, rfl⟩

theorem prod_ker_comp_finProdFinEquiv {d r' : ℕ} (q₂ : Fin d → {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) :
    ∏ l : Fin (d * r'), (q₂ (finProdFinEquiv.symm l).1).1.ker = ∏ ml : Fin d × Fin r', (q₂ ml.1).1.ker :=
  Fintype.prod_equiv finProdFinEquiv.symm _ _ fun _ => rfl

end S2

section Frame

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {M' : ℕ} {B' : Fin M' → Type u} [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
  (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
  (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  {C₁ C₂ : Scheme.{u}} {c₁ : C₁ ⟶ Spec (CommRingCat.of Ω)} {c₂ : C₂ ⟶ Spec (CommRingCat.of Ω)}
  (i₁ : SchemeHomOver c₁ (pullback.snd c (specMap R Ω))) (i₂ : SchemeHomOver c₂ (pullback.snd c (specMap R Ω)))
  (Utr cc : Set ↥(pullback c (specMap R Ω)))
  (h7 : Set.range i₁.1.base ∩ Utr = cc) (h8 : Set.range i₂.1.base ∩ Utr = Utr \ cc)
  (hz'ε : ∀ i, (pullback.fst c (specMap R Ω)).base ⁻¹' Set.range (z' i).base ⊆ Utr \ cc)

include h7 h8 hz'ε in

theorem range_ptOf_subset_range_diff (i : Fin M') (ψ : B' i →ₐ[R] Ω) :
    Set.range (ptOf c z' hz' i ψ).1.base ⊆ Set.range i₂.1.base \ Set.range i₁.1.base :=
  subset_range_diff_of_subset_diff h7 h8 ((range_ptOf_subset c z' hz' i ψ).trans (hz'ε i))

include h7 h8 hz'ε in
theorem range_ptOf_subset_range_snd (i : Fin M') (ψ : B' i →ₐ[R] Ω) :
    Set.range (ptOf c z' hz' i ψ).1.base ⊆ Set.range i₂.1.base :=
  fun _ hz => (range_ptOf_subset_range_diff c z' hz' i₁ i₂ Utr cc h7 h8 hz'ε i ψ hz).1

include hz' h7 h8 hz'ε in

theorem range_subset_of_fst_eq (i : Fin M') (ψ : B' i →ₐ[R] Ω)
    (v : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // p ≫ pullback.snd c (specMap R Ω) = 𝟙 _})
    (hv : v.1 ≫ pullback.fst c (specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i) :
    Set.range v.1.base ⊆ Set.range i₂.1.base \ Set.range i₁.1.base ∧ Set.range v.1.base ⊆ Utr := by
  have e := eq_ptOf_of_fst_eq c z' hz' i ψ v hv
  subst e
  exact ⟨range_ptOf_subset_range_diff c z' hz' i₁ i₂ Utr cc h7 h8 hz'ε i ψ,
    fun _ hz => ((range_ptOf_subset c z' hz' i ψ).trans (hz'ε i) hz).1⟩

theorem card_blk_le_of_equiv [∀ i, Fintype (B' i →ₐ[R] Ω)] [IsClosedImmersion i₂.1]
    (hon : ∀ (i : Fin M') (ψ : B' i →ₐ[R] Ω), Set.range (ptOf c z' hz' i ψ).1.base ⊆ Set.range i₂.1.base)
    {deg' : Fin M' → ℕ} (eB' : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i)) (i : Fin M') :
    (blk c z' hz' i₂ hon i).card ≤ deg' i :=
  (card_blk_le c z' hz' i₂ hon i).trans (by rw [Fintype.card_congr (eB' i), Fintype.card_fin])

end Frame

namespace CrossSnd

theorem ker_le_ker_of_range_subset {X X' Z : Scheme.{u}} (f : X ⟶ Z) (g : X' ⟶ Z) [IsClosedImmersion f] [QuasiCompact g]
    [IsReduced X'] (h : Set.range g.base ⊆ Set.range f.base) : f.ker ≤ g.ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U s hs
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hs ⊢
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen]
  have hempty : ∀ x : X', g.base x ∉ Z.basicOpen s := by
    intro x hx
    obtain ⟨w, hw⟩ := h ⟨x, rfl⟩
    have hw' : w ∈ f ⁻¹ᵁ Z.basicOpen s := by
      change f.base w ∈ Z.basicOpen s
      rw [hw]; exact hx
    rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero] at hw'
    exact hw'
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact hempty x

theorem section_eq_of_base_eq {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    (p p' : Spec (CommRingCat.of k) ⟶ C) (hp : p ≫ c = 𝟙 _) (hp' : p' ≫ c = 𝟙 _)
    (h : p.base (IsLocalRing.closedPoint k) = p'.base (IsLocalRing.closedPoint k)) : p = p' := by
  haveI : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id c p hp
  have hrange : Set.range p'.base ⊆ Set.range p.base := by
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact ⟨IsLocalRing.closedPoint k, h⟩
  let g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
    IsClosedImmersion.lift p p' (ker_le_ker_of_range_subset p p' hrange)
  have hg : g ≫ p = p' := IsClosedImmersion.lift_fac _ _ _
  have hg1 : g = 𝟙 _ := by
    have := congrArg (· ≫ c) hg
    simp only [Category.assoc, hp, hp', Category.comp_id] at this
    exact this
  rw [← hg, hg1, Category.id_comp]

end CrossSnd

theorem crossSnd
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType c₁] [LocallyOfFiniteType c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∃ N₂ : Finset {p : Spec (CommRingCat.of k) ⟶ C₂ // p ≫ c₂ = 𝟙 _},
      N₂.card = n ∧ (∀ p ∈ N₂, Set.range (p.1 ≫ i₂.1).base ⊆ Set.range i₁.1.base) ∧
      ∀ p : {p : Spec (CommRingCat.of k) ⟶ C₂ // p ≫ c₂ = 𝟙 _}, Set.range (p.1 ≫ i₂.1).base ⊆ Set.range i₁.1.base → p ∈ N₂ := by
  classical
  obtain ⟨p₁, p₂, hinj, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ n hn hn0

  have hinj2 : Function.Injective p₂ := by
    intro j j' hjj
    apply hinj
    have e1 : (p₁ j).1 ≫ i₁.1 = (p₁ j').1 ≫ i₁.1 := by rw [hnode j, hnode j', hjj]
    have e2 : (p₁ j).1 = (p₁ j').1 := (cancel_mono i₁.1).mp e1
    change (p₁ j).1.base _ = (p₁ j').1.base _
    rw [e2]
  refine ⟨Finset.univ.image p₂, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj2, Finset.card_univ, Fintype.card_fin]
  · intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    rw [← hnode j]
    rintro _ ⟨t, rfl⟩
    exact ⟨(p₁ j).1.base t, by rw [Scheme.Hom.comp_base]; rfl⟩
  · intro p hp

    obtain ⟨q₁, hq₁⟩ := hp ⟨IsLocalRing.closedPoint k, rfl⟩
    have hc : i₁.1.base q₁ = i₂.1.base (p.1.base (IsLocalRing.closedPoint k)) := by
      rw [hq₁]; rfl
    obtain ⟨j, -, hj₂⟩ := hinter q₁ _ hc
    have hpj : p.1 = (p₂ j).1 := CrossSnd.section_eq_of_base_eq c₂ p.1 (p₂ j).1 p.2 (p₂ j).2 hj₂
    have : p = p₂ j := Subtype.ext hpj
    rw [this]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)

theorem h0h1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[k] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[k] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒲, hU0, hU1, h0, h1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
      (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒲 = 𝒱 := by
    cases 𝒲; cases 𝒱
    simp only at hU0 hU1
    subst hU0; subst hU1
    rfl
  exact ⟨h0, h1⟩

theorem range_eq_singleton {Ω : Type u} [Field Ω] {X : Scheme.{u}} (s : Spec (CommRingCat.of Ω) ⟶ X) :
    Set.range s.base = {s.base (IsLocalRing.closedPoint Ω)} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rfl
  · rintro rfl; exact ⟨_, rfl⟩

end AlgebraicGeometry.RelPicard.K3Far
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard.K3Far"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry"

open AlgebraicGeometry.RelPicard.K3Far in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {M' : ℕ} (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (deg' : Fin M' → ℕ) {b : ℕ} (hb : 1 ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB' : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i))

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

    (hz'ε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z' i).base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \
        connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
          (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (r' γ₂ e₂ : ℕ) (i₀ : Fin M') (𝒱₂ : C₂.TwoAffineOpenCover)
    (hγ₂ : Module.finrank Ω (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf)).H1 = γ₂)
    (he₂ : γ₂ + e₂ = r' * deg' i₀) (hr₂ : 2 * γ₂ ≤ r' * deg' i₀)
    (hcount₂ : (n + 1) * (r' * b) * b ^ e₂ + e₂ + 1 < M')

    (q : Fin (deg' i₀) → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
    (hq : ∀ m, (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
      Spec.map (CommRingCat.ofHom ((eB' i₀).symm m).toRingHom) ≫ z' i₀)

    (r : ℕ)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a' : Fin e₂ → Fin M', Function.Injective a' ∧ (∀ j, a' j ≠ i₀) ∧
      ∀ (v' : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
          (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →
        ∀ {e₁ : ℕ} (v : Fin e₁ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, Set.range (v j).1.base ⊆
            (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₂.1.base) →
          ∀ 𝒲₂ : C₂.TwoAffineOpenCover,
            (Subsingleton (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj
                (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)))).H1 ∧
              Module.finrank Ω (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj
                (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)))).H0 = 1) ∧
            ∀ p : Spec (CommRingCat.of Ω) ⟶ C₂, p ≫ c₂ = 𝟙 _ →
              Set.range (p ≫ i₂.1).base ⊆ Set.range i₁.1.base →
              Module.finrank Ω (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj
                (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗ (p.ker).module)).H0 = 0 := by
  classical
  obtain ⟨hcov, hred, hn, hn0, hε, h6, h7, h8, ⟨W₁, hW₁, hoi₁⟩, ⟨W₂, hW₂, hoi₂⟩⟩ := hbadΩ
  haveI : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
  haveI : ∀ i, Fintype (B' i →ₐ[R] Ω) := fun i => Fintype.ofEquiv _ (eB' i).symm
  have ht : r' * deg' i₀ = deg' i₀ * r' := Nat.mul_comm _ _
  rw [ht] at he₂ hr₂

  have hon := range_ptOf_subset_range_snd c z' hz' i₁ i₂ _ _ h7 h8 hz'ε

  obtain ⟨N₂, hN₂card, -, hN₂all⟩ := crossSnd Ω (pullback.snd c (specMap R Ω)) c₁ c₂ i₁ i₂ hred n hn hn0
  let p₂ : Fin n → {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} :=
    fun m => (N₂.equivFin.symm (Fin.cast hN₂card.symm m)).1
  have hp₂surj : ∀ p ∈ N₂, ∃ m, p₂ m = p := fun p hp =>
    ⟨Fin.cast hN₂card (N₂.equivFin ⟨p, hp⟩), by simp [p₂]⟩

  have hqpt : ∀ m, q m = ptOf c z' hz' i₀ ((eB' i₀).symm m) := fun m =>
    eq_ptOf_of_fst_eq c z' hz' i₀ _ (q m) (hq m)
  have hqon : ∀ m, Set.range (q m).1.base ⊆ Set.range i₂.1.base := fun m => by rw [hqpt m]; exact hon i₀ _
  let q₂ : Fin (deg' i₀) → {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} :=
    fun m => liftSnd c i₂ (q m) (hqon m)
  have hq₂ : ∀ m, (q₂ m).1 ≫ i₂.1 = (q m).1 := fun m => liftSnd_comp c i₂ (q m) (hqon m)

  let S : Fin (n + 1) → Finset {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} :=
    Fin.cases ∅ (fun m => {p₂ m})
  have hS0 : S 0 = ∅ := Fin.cases_zero
  have hSs : ∀ m : Fin n, S m.succ = {p₂ m} := fun m => Fin.cases_succ m
  have hScard : ∀ κ, (S κ).card ≤ 1 := fun κ => by
    refine Fin.cases ?_ (fun m => ?_) κ
    · rw [hS0, Finset.card_empty]; exact Nat.zero_le _
    · rw [hSs, Finset.card_singleton]
  have hS : ∀ κ, 2 * γ₂ + (S κ).card ≤ deg' i₀ * r' + 1 := fun κ => by have := hScard κ; omega
  have heS : ∀ κ, e₂ + (S κ).card + γ₂ ≤ deg' i₀ * r' + 1 := fun κ => by have := hScard κ; omega
  let Bl : {i : Fin M' // i ≠ i₀} → Finset {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} :=
    fun i => blk c z' hz' i₂ hon i.1
  have hdisj : ∀ i i' : {i : Fin M' // i ≠ i₀}, i ≠ i' → Disjoint (Bl i) (Bl i') := fun i i' h =>
    disjoint_blk c z' hz' i₂ hon hz'disj (fun e => h (Subtype.ext e))
  have hBb : ∀ i : {i : Fin M' // i ≠ i₀}, (Bl i).card ≤ b := fun i =>
    (card_blk_le_of_equiv c z' hz' i₂ hon eB' i.1).trans (hdeg'b i.1)
  have hcardι : Fintype.card {i : Fin M' // i ≠ i₀} = M' - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  have hmul : (n + 1) * (deg' i₀ * r') * b ^ e₂ ≤ (n + 1) * (r' * b) * b ^ e₂ :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (hdeg'b i₀)))
  have hcard : (n + 1) * (deg' i₀ * r') * b ^ e₂ + e₂ < Fintype.card {i : Fin M' // i ≠ i₀} := by
    rw [hcardι]; omega
  obtain ⟨a, ha, hK6⟩ :=
    AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
      Ω c₂ γ₂ 𝒱₂ hγ₂ ((Scheme.Modules.pullback i₂.1).obj L₀) (hL₀.pullback i₂.1) (h0.pullback i₂.1 i₂.2)
      (fun l : Fin (deg' i₀ * r') => q₂ (finProdFinEquiv.symm l).1) S e₂ hS heS Bl hdisj hb hBb hcard
  refine ⟨fun j => (a j).1, fun j j' h => ha (Subtype.ext h), fun j => (a j).2, ?_⟩
  intro v' hv' e₁ v hv 𝒲₂
  choose ψ hψ using hv'
  have hv'geo := fun j => range_subset_of_fst_eq c z' hz' i₁ i₂ _ _ h7 h8 hz'ε (a j).1 (ψ j) (v' j) (hψ j)
  let v₂ : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ C₂ // p ≫ c₂ = 𝟙 _} :=
    fun j => liftSnd c i₂ (v' j) (fun z hz => ((hv'geo j).1 hz).1)
  have hv₂ : ∀ j, (v₂ j).1 ≫ i₂.1 = (v' j).1 := fun j => liftSnd_comp c i₂ (v' j) _
  have hmem : ∀ j, v₂ j ∈ Bl (a j) := fun j =>
    liftSnd_mem_blk c z' hz' i₂ hon (a j).1 (ψ j) (v' j) (hψ j) _

  have ε₀fst : (sectionFibrePoint ε (specMap R Ω)).1 ≫ pullback.fst c (specMap R Ω) = specMap R Ω ≫ ε.1 :=
    pullback.lift_fst _ _ _
  have hUtr : ∀ (s : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω)),
      Set.range (s ≫ pullback.fst c (specMap R Ω)).base ⊆ (U : Set C) →
      Set.range s.base ⊆ ((pullback.fst c (specMap R Ω) ⁻¹ᵁ U : (pullback c (specMap R Ω)).Opens) :
        Set ↥(pullback c (specMap R Ω))) := by
    rintro s hs _ ⟨t, rfl⟩
    exact hs ⟨t, by rw [Scheme.Hom.comp_base]; rfl⟩
  have hε₀U : Set.range (sectionFibrePoint ε (specMap R Ω)).1.base ⊆
      ((pullback.fst c (specMap R Ω) ⁻¹ᵁ U : (pullback c (specMap R Ω)).Opens) : Set ↥(pullback c (specMap R Ω))) := by
    refine hUtr _ ?_
    rw [ε₀fst]
    rintro _ ⟨t, rfl⟩
    exact hεU ⟨(specMap R Ω).base t, by rw [Scheme.Hom.comp_base]; rfl⟩
  have hε₀ : Set.range (sectionFibrePoint ε (specMap R Ω)).1.base ⊆ (Set.range i₂.1.base)ᶜ := by
    rw [range_eq_singleton]; rintro _ rfl; exact hε.2
  have hε₀i : (sectionFibrePoint ε (specMap R Ω)).1.ker.IsInvertible :=
    isInvertible_ker_of_mem c U (specMap R Ω) _ (sectionFibrePoint ε (specMap R Ω)).2 hε₀U
  have hvX : ∀ j, Set.range (v j).1.base ⊆ (Set.range i₂.1.base)ᶜ := fun j z hz => (hv j hz).2
  have hvi : ∀ j, (v j).1.ker.IsInvertible := fun j =>
    isInvertible_ker_of_mem c U (specMap R Ω) _ (v j).2 (fun z hz => (hv j hz).1)
  have h6' : ∀ {Sx : Set ↥(pullback c (specMap R Ω))}, Sx ⊆ Set.range i₂.1.base \ Set.range i₁.1.base →
      Sx ⊆ (Set.range i₁.1.base)ᶜ := fun h z hz => (h hz).2
  have hqdiff : ∀ m, Set.range (q m).1.base ⊆ Set.range i₂.1.base \ Set.range i₁.1.base := fun m => by
    rw [hqpt m]; exact range_ptOf_subset_range_diff c z' hz' i₁ i₂ _ _ h7 h8 hz'ε i₀ _
  have hqX : ∀ m, Set.range (q m).1.base ⊆ (Set.range i₁.1.base)ᶜ := fun m => h6' (hqdiff m)
  have hqi : ∀ m, (q m).1.ker.IsInvertible := fun m =>
    isInvertible_ker_of_mem c U (specMap R Ω) _ (q m).2 (fun z hz => by
      rw [hqpt m] at hz
      exact ((range_ptOf_subset c z' hz' i₀ _).trans (hz'ε i₀) hz).1)
  have hv'X : ∀ j, Set.range (v' j).1.base ⊆ (Set.range i₁.1.base)ᶜ := fun j => h6' (hv'geo j).1
  have hv'i : ∀ j, (v' j).1.ker.IsInvertible := fun j =>
    isInvertible_ker_of_mem c U (specMap R Ω) _ (v' j).2 (hv'geo j).2
  obtain ⟨eK5⟩ := AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_iso_snd Ω
    (pullback.snd c (specMap R Ω)) c₁ c₂ i₁ i₂ W₂ hW₂ hoi₂ L₀ hL₀ r (sectionFibrePoint ε (specMap R Ω)) hε₀ hε₀i
    v hvX hvi r' q hqX hqi q₂ hq₂ v' hv'X hv'i v₂ hv₂

  have hK60 := hK6 v₂ hmem 0 𝒲₂
  rw [hS0, Finset.prod_empty, mul_one, Finset.card_empty, add_zero, prod_ker_comp_finProdFinEquiv] at hK60
  obtain ⟨h0eq, h1sub⟩ := hK60
  obtain ⟨⟨f0⟩, ⟨f1⟩⟩ := h0h1_congr c₂ 𝒲₂ eK5
  refine ⟨⟨(Equiv.subsingleton_congr f1.toEquiv).mpr h1sub, ?_⟩, ?_⟩
  · rw [f0.finrank_eq]; omega

  intro p hp hrange
  obtain ⟨m, hm⟩ := hp₂surj ⟨p, hp⟩ (hN₂all ⟨p, hp⟩ hrange)
  have hK6m := hK6 v₂ hmem m.succ 𝒲₂
  rw [hSs, Finset.prod_singleton, Finset.card_singleton, prod_ker_comp_finProdFinEquiv, hm] at hK6m
  obtain ⟨h0m, -⟩ := hK6m
  have h0m' : Module.finrank Ω (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj L₀ ⊗
      ((∏ ml : Fin (deg' i₀) × Fin r', (q₂ ml.1).1.ker).invModule ⊗ ((∏ j, (v₂ j).1.ker) * p.ker).module))).H0
      + e₂ + 1 + γ₂ = deg' i₀ * r' + 1 := h0m
  have hVi : (∏ j, (v₂ j).1.ker).IsInvertible :=
    Finset.prod_induction _ (fun I : C₂.IdealSheafData => I.IsInvertible) (fun _ _ h h' => h.mul h')
      Scheme.IdealSheafData.isInvertible_top
      (fun j _ => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c₂) (v₂ j).1 (v₂ j).2)
  have hpi : p.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c₂) p hp
  obtain ⟨μ, -⟩ := Scheme.IdealSheafData.IsInvertible.exists_tensor_iso_mul_module hVi hpi
  let eBr := (eK5 ⊗ᵢ Iso.refl (p.ker).module) ≪≫ α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ (α_ _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ μ)))
  obtain ⟨⟨g0⟩, -⟩ := h0h1_congr c₂ 𝒲₂ eBr
  rw [g0.finrank_eq]
  omega

end
end S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration (solution)
