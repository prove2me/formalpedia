-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/be23c5d0-604e-56e9-8a32-69d216781853

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
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_finrank_H1_add_finrank_H1_add_eq_of_finrank_H1_unit_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Hom GeometricallyIntegral Scheme.Hom.preimage_inf Scheme.Pullback.range_fst Spec Spec.map Scheme Smooth pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.preimage_sup Scheme.Modules pullbackRestrictIsoRestrict IsAffineHom geometrically Scheme.IdealSheafData Scheme.Modules.IsInvertible SmoothProperCurve.specMap Scheme.Modules.zeroSchemeIdeal Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.IdealSheafData.IsInvertible.mul TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration TwoGluedCurves.finrank_H1_add_finrank_H1_add_eq_of_finrank_H1_unit_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens Scheme.Modules.IsInvertible.tensor Scheme.IdealSheafData.IsInvertible.isInvertible_invModule Scheme.IdealSheafData.IsInvertible.isInvertible_module"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "IsAlgEquivZero sectionFibrePoint exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration"
namespace N1BadFibre
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

def comapCover {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i] (𝒲 : X.TwoAffineOpenCover) :
    Y.TwoAffineOpenCover where
  U0 := i ⁻¹ᵁ 𝒲.U0
  U1 := i ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage _
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage _
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage _

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

end AlgebraicGeometry.RelPicard.N1BadFibre

end

open AlgebraicGeometry.RelPicard.N1BadFibre in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i)
    {b : ℕ} (hdegb : ∀ i, deg i ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)

    (g r r' e : ℕ) (i₀ : Fin M') (hr : 2 * g + 1 ≤ r) (hr' : 2 * g + 1 ≤ r') (he : g + e = r + r' * deg' i₀)
    (hcount : (g + 2) * (r + r' * b) * b ^ e + e < M) (hcount' : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M')

    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i)) (eB' : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i))
    [IsProper (pullback.snd c (SmoothProperCurve.specMap R Ω))]
    [IsReduced (pullback c (SmoothProperCurve.specMap R Ω))]
    (hns : ¬ Smooth (pullback.snd c (SmoothProperCurve.specMap R Ω)))

    (𝒲₀ : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover)

    (q : Fin (deg' i₀) → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
        p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
    (hq : ∀ m, (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
      Spec.map (CommRingCat.ofHom ((eB' i₀).symm m).toRingHom) ≫ z' i₀)

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))

    (hzε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base ⊆
      connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))
    (hz'ε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z' i).base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \
        connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
          (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (hH0 : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω ↥(𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H0 = 1)
    (hg : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H1 = g)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ (e₁ e₂ : ℕ) (_ : e₁ + e₂ = e) (a : Fin e₁ → Fin M) (a' : Fin e₂ → Fin M'),
      Function.Injective a ∧ Function.Injective a' ∧ (∀ j, a' j ≠ i₀) ∧
      ∀ (v : Fin e₁ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
        (v' : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
          (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →

        (∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))).H1) ∧
        (∀ σ : 𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules ⟶
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)),
          σ ≠ 0 →
          ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆
            (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) :
              Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) := by
  classical
  haveI : IsSeparated c := inferInstance

  obtain ⟨C₁, C₂, c₁, c₂, hp₁, hsm₁, hgi₁, hp₂, hsm₂, hgi₂, i₁, i₂, hci₁, hci₂, n, hbadΩ⟩ :=
    hbad Ω (SmoothProperCurve.specMap R Ω) hns
  have hbadΩ' := hbadΩ
  obtain ⟨hcov, hcr, hn, hn0, hεpl, hUtr, hC₁U, hC₂U, -, -⟩ := hbadΩ'

  let 𝒱₁ : C₁.TwoAffineOpenCover := comapCover i₁.1 𝒲₀
  let 𝒱₂ : C₂.TwoAffineOpenCover := comapCover i₂.1 𝒲₀

  have hG := AlgebraicGeometry.TwoGluedCurves.finrank_H1_add_finrank_H1_add_eq_of_finrank_H1_unit_eq Ω
    (pullback.snd c (SmoothProperCurve.specMap R Ω)) c₁ c₂ i₁ i₂ hcov hcr n hn hn0 𝒲₀ 𝒱₁ 𝒱₂ g (hH0 𝒲₀) (hg 𝒲₀)
  generalize hγ₁ : Module.finrank Ω (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf)).H1 = γ₁ at hG
  generalize hγ₂ : Module.finrank Ω (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf)).H1 = γ₂ at hG

  have hM0 : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hcount
  have hb : 1 ≤ b := (hdeg ⟨0, hM0⟩).trans (hdegb ⟨0, hM0⟩)
  have hd : 1 ≤ deg' i₀ := hdeg' i₀
  have hρ : r' ≤ r' * deg' i₀ := Nat.le_mul_of_pos_right _ hd
  have hρb : r' * deg' i₀ ≤ r' * b := Nat.mul_le_mul_left _ (hdeg'b i₀)
  generalize hρdef : r' * deg' i₀ = ρ at he hρ hρb
  have hsplit : (r + 1 - γ₁ - n) + (ρ - γ₂) = e := by omega
  have hpow₁ : b ^ (r + 1 - γ₁ - n) ≤ b ^ e := Nat.pow_le_pow_right hb (by omega)
  have hpow₂ : b ^ (ρ - γ₂) ≤ b ^ e := Nat.pow_le_pow_right hb (by omega)
  have hcount₁ : r * b ^ (r + 1 - γ₁ - n) + (r + 1 - γ₁ - n) < M := by
    have h1 : r * b ^ (r + 1 - γ₁ - n) ≤ (g + 2) * (r + r' * b) * b ^ e :=
      calc r * b ^ (r + 1 - γ₁ - n) ≤ r * b ^ e := Nat.mul_le_mul_left _ hpow₁
        _ ≤ (g + 2) * (r + r' * b) * b ^ e := by
          apply Nat.mul_le_mul_right
          calc r ≤ 1 * (r + r' * b) := by omega
            _ ≤ (g + 2) * (r + r' * b) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hcount₂ : (n + 1) * (r' * b) * b ^ (ρ - γ₂) + (ρ - γ₂) + 1 < M' := by
    have h1 : (n + 1) * (r' * b) * b ^ (ρ - γ₂) ≤ (g + 2) * (r + r' * b) * b ^ e :=
      calc (n + 1) * (r' * b) * b ^ (ρ - γ₂) ≤ (n + 1) * (r' * b) * b ^ e := Nat.mul_le_mul_left _ hpow₂
        _ ≤ (g + 2) * (r + r' * b) * b ^ e := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul (by omega) (by omega)
    omega

  have hN : Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base = Set.range i₁.1.base ∩ Set.range i₂.1.base := by
    rw [show (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base = (pullback.fst i₁.1 i₂.1).base ≫ i₁.1.base from rfl,
      TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst, Set.image_preimage_eq_range_inter]

  have hoff : ∀ y : ↥(pullback c (SmoothProperCurve.specMap R Ω)), y ∈ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) →
      y ∈ Set.range i₁.1.base → y ∉ Set.range i₂.1.base := by
    intro y hyU hy₁ hy₂
    rw [hUtr, hN] at hyU
    exact hyU ⟨hy₁, hy₂⟩

  have hfarpt : ∀ (i : Fin M') (p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
      (∃ f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (B' i)), p.1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = f ≫ z' i) →
      Set.range p.1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ∧
      Set.range p.1.base ⊆ (Set.range i₁.1.base)ᶜ := by
    rintro i p ⟨f, hf⟩
    have hmem : ∀ t, p.1.base t ∈ (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z' i).base := by
      intro t
      show (p.1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω)).base t ∈ Set.range (z' i).base
      rw [hf]; exact ⟨f.base t, rfl⟩
    have h2 := fun t => hz'ε i (hmem t)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨t, rfl⟩; exact (h2 t).1
    · rintro _ ⟨t, rfl⟩ hy₁
      have hyU := (h2 t).1
      have hy₂ : p.1.base t ∈ Set.range i₂.1.base := by
        have : p.1.base t ∈ Set.range i₂.1.base ∩ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by rw [hC₂U]; exact h2 t
        exact this.1
      exact hoff _ hyU hy₁ hy₂

  have hnearpt : ∀ (i : Fin M) (p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
      (∃ f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (B i)), p.1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = f ≫ z i) →
      Set.range p.1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ∧
      Set.range p.1.base ⊆ (Set.range i₂.1.base)ᶜ := by
    rintro i p ⟨f, hf⟩
    have hmem : ∀ t, p.1.base t ∈ (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base := by
      intro t
      show (p.1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω)).base t ∈ Set.range (z i).base
      rw [hf]; exact ⟨f.base t, rfl⟩
    have h2 : ∀ t, p.1.base t ∈ Set.range i₁.1.base ∩ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
      intro t; rw [hC₁U]; exact hzε i (hmem t)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨t, rfl⟩; exact (h2 t).2
    · rintro _ ⟨t, rfl⟩ hy₂; exact hoff _ (h2 t).2 (h2 t).1 hy₂
  have hq₁ : ∀ m, Set.range (q m).1.base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₁.1.base :=
    fun m y hy => ⟨(hfarpt i₀ (q m) ⟨_, hq m⟩).1 hy, (hfarpt i₀ (q m) ⟨_, hq m⟩).2 hy⟩

  have hεtr : Set.range (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) := by
    rintro _ ⟨t, rfl⟩
    show ((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω)).base t ∈ (U : Set C)
    rw [show (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = (SmoothProperCurve.specMap R Ω) ≫ ε.1 from pullback.lift_fst _ _ _]
    exact hεU ⟨_, rfl⟩

  obtain ⟨a, ha, hnear⟩ :=
    AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
      R c ε U hεU B z hz hzdisj deg hb hdegb Ω eB c₁ c₂ i₁ i₂ n hbadΩ hzε r γ₁ (r + 1 - γ₁ - n) 𝒱₁ hγ₁ (by omega) (by omega)
      hcount₁ r' q hq₁ L₀ hL₀ h0
  obtain ⟨a', ha', hai₀, hfar⟩ :=
    AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
      R c ε U hεU B' z' hz' hz'disj deg' hb hdeg'b Ω eB' c₁ c₂ i₁ i₂ n hbadΩ hz'ε r' γ₂ (ρ - γ₂) i₀ 𝒱₂ hγ₂ (by omega) (by omega)
      hcount₂ q hq r L₀ hL₀ h0
  refine ⟨r + 1 - γ₁ - n, ρ - γ₂, hsplit, a, a', ha, ha', hai₀, ?_⟩
  intro v v' hv hv'
  have hv'off : ∀ j, Set.range (v' j).1.base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₁.1.base := fun j y hy => by
    obtain ⟨ψ, hψ⟩ := hv' j
    exact ⟨(hfarpt (a' j) (v' j) ⟨_, hψ⟩).1 hy, (hfarpt (a' j) (v' j) ⟨_, hψ⟩).2 hy⟩
  have hvoff : ∀ j, Set.range (v j).1.base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₂.1.base := fun j y hy => by
    obtain ⟨ψ, hψ⟩ := hv j
    exact ⟨(hnearpt (a j) (v j) ⟨_, hψ⟩).1 hy, (hnearpt (a j) (v j) ⟨_, hψ⟩).2 hy⟩
  obtain ⟨h1a, h1b⟩ := hnear v hv v' hv'off 𝒱₁
  obtain ⟨h2, h3⟩ := hfar v' hv' v hvoff 𝒱₂

  have hker : ∀ p : {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}, Set.range p.1.base ⊆ (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) → p.1.ker.IsInvertible :=
    fun p hp => isInvertible_ker_of_mem c U (SmoothProperCurve.specMap R Ω) p.1 p.2 hp
  have hinv : Scheme.Modules.IsInvertible
      (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
        ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) := by
    refine hL₀.tensor (Scheme.Modules.IsInvertible.tensor ?_ ?_)
    · refine Scheme.IdealSheafData.IsInvertible.isInvertible_invModule (Scheme.IdealSheafData.IsInvertible.mul ?_ ?_)
      · exact (hker _ hεtr).pow r
      · refine (Finset.prod_induction _ (fun I : (pullback c (SmoothProperCurve.specMap R Ω)).IdealSheafData => I.IsInvertible)
          (fun _ _ h h' => h.mul h') Scheme.IdealSheafData.isInvertible_top (fun m _ => ?_)).pow r'
        exact hker (q m) (hfarpt i₀ (q m) ⟨_, hq m⟩).1
    · refine Scheme.IdealSheafData.IsInvertible.isInvertible_module (Scheme.IdealSheafData.IsInvertible.mul ?_ ?_)
      · exact Finset.prod_induction _ (fun I : (pullback c (SmoothProperCurve.specMap R Ω)).IdealSheafData => I.IsInvertible)
          (fun _ _ h h' => h.mul h') Scheme.IdealSheafData.isInvertible_top
          (fun j _ => by obtain ⟨ψ, hψ⟩ := hv j; exact hker (v j) (hnearpt (a j) (v j) ⟨_, hψ⟩).1)
      · exact Finset.prod_induction _ (fun I : (pullback c (SmoothProperCurve.specMap R Ω)).IdealSheafData => I.IsInvertible)
          (fun _ _ h h' => h.mul h') Scheme.IdealSheafData.isInvertible_top
          (fun j _ => by obtain ⟨ψ, hψ⟩ := hv' j; exact hker (v' j) (hfarpt (a' j) (v' j) ⟨_, hψ⟩).1)

  obtain ⟨hH1, hsupp⟩ :=
    AlgebraicGeometry.TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict Ω
      (pullback.snd c (SmoothProperCurve.specMap R Ω)) c₁ c₂ i₁ i₂ hcov hcr n hn hn0 _ hinv 𝒱₁ 𝒱₂ ⟨h1a, h1b⟩ h2 h3
  exact ⟨hH1, fun σ hσ => (hsupp σ hσ).trans (le_of_eq hUtr.symm)⟩

end S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration (solution)
