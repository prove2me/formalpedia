-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ef8e14cb-5de5-5220-a0c9-53e3742c322e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicCurve~genus~cechDiff AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec IsIntegral Spec.map Scheme Spec.map_id Scheme.Modules Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap SmoothProperCurve.specMap Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card"
namespace WGenBlocks
p2m_open "AlgebraicGeometry"

variable {A : Type u} [CommRing A] {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of A))
  {R' : Type u} [CommRing R'] [Algebra A R']
  {M : ℕ} {B : Fin M → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  {deg : Fin M → ℕ} (φ : ∀ i, R' ⊗[A] (B i) ≃ₐ[R'] (Fin (deg i) → R'))
  (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C') (hz : ∀ i, z i ≫ c' = specMap A (B i))
  {Ω : Type u} [Field Ω] [Algebra A Ω] (t : R' →ₐ[A] Ω)

def homR (i : Fin M) (m : Fin (deg i)) : B i →+* Ω :=
  t.toRingHom.comp ((Pi.evalRingHom (fun _ : Fin (deg i) => R') m).comp
    ((φ i).toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := A) (A := R') (B := B i)).toRingHom))

theorem homR_comp_algebraMap (i : Fin M) (m : Fin (deg i)) :
    (homR φ t i m).comp (algebraMap A (B i)) = algebraMap A Ω := by
  ext a
  simp only [homR, RingHom.coe_comp, Function.comp_apply]
  have h1 : (Algebra.TensorProduct.includeRight (R := A) (A := R') (B := B i)).toRingHom (algebraMap A (B i) a) =
      algebraMap R' (R' ⊗[A] B i) (algebraMap A R' a) := by
    show Algebra.TensorProduct.includeRight (R := A) (A := R') (B := B i) (algebraMap A (B i) a) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A R' (R' ⊗[A] B i)]
  rw [h1]
  have h2 : (φ i).toRingEquiv.toRingHom (algebraMap R' (R' ⊗[A] B i) (algebraMap A R' a)) =
      algebraMap R' (Fin (deg i) → R') (algebraMap A R' a) := (φ i).commutes _
  rw [h2, Pi.evalRingHom_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact t.commutes a

def pt (i : Fin M) (m : Fin (deg i)) :
    {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (homR φ t i m)) ≫ z i) (𝟙 _) (by
      rw [Category.assoc, hz i, Category.id_comp]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, homR_comp_algebraMap]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem pt_fst (i : Fin M) (m : Fin (deg i)) :
    (pt c' φ z hz t i m).1 ≫ pullback.fst c' (specMap A Ω) = Spec.map (CommRingCat.ofHom (homR φ t i m)) ≫ z i :=
  pullback.lift_fst _ _ _

def block (i : Fin M) :
    Finset {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} := by
  classical
  exact Finset.univ.image (pt c' φ z hz t i)

theorem pt_mem_block (i : Fin M) (m : Fin (deg i)) : pt c' φ z hz t i m ∈ block c' φ z hz t i := by
  classical
  unfold block
  exact Finset.mem_image_of_mem _ (Finset.mem_univ m)

theorem card_block_le (i : Fin M) : (block c' φ z hz t i).card ≤ deg i := by
  classical
  unfold block
  exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])

theorem block_nonempty (i : Fin M) (h : 1 ≤ deg i) : (block c' φ z hz t i).Nonempty :=
  ⟨_, pt_mem_block c' φ z hz t i ⟨0, h⟩⟩

theorem mem_block_iff (i : Fin M)
    (q : {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _}) :
    q ∈ block c' φ z hz t i ↔ ∃ m, pt c' φ z hz t i m = q := by
  classical
  unfold block
  simp

theorem range_subset_of_mem_block (i : Fin M)
    (q : {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _})
    (hq : q ∈ block c' φ z hz t i) :
    Set.range (q.1 ≫ pullback.fst c' (specMap A Ω)).base ⊆ Set.range (z i).base := by
  obtain ⟨m, rfl⟩ := (mem_block_iff c' φ z hz t i q).mp hq
  rw [pt_fst]
  rintro _ ⟨y, rfl⟩
  exact ⟨(Spec.map (CommRingCat.ofHom (homR φ t i m))).base y, rfl⟩

theorem disjoint_block (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    {i j : Fin M} (hij : i ≠ j) : Disjoint (block c' φ z hz t i) (block c' φ z hz t j) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqi hqj
  have hi := range_subset_of_mem_block c' φ z hz t i q hqi
  have hj := range_subset_of_mem_block c' φ z hz t j q hqj
  have hpt : (q.1 ≫ pullback.fst c' (specMap A Ω)).base (IsLocalRing.closedPoint Ω) ∈
      Set.range (z i).base ∩ Set.range (z j).base := ⟨hi ⟨_, rfl⟩, hj ⟨_, rfl⟩⟩
  exact Set.disjoint_iff.mp (hdisj hij) hpt

include hz in

theorem exists_blocks (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) :
    ∃ Bk : Fin M → Finset {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) //
        q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _},
      (∀ i, (Bk i).card ≤ deg i) ∧ (∀ i, 1 ≤ deg i → (Bk i).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) ∧
      (∀ i (m : Fin (deg i)), ∃ q ∈ Bk i,
        q.1 ≫ pullback.fst c' (specMap A Ω) = Spec.map (CommRingCat.ofHom (homR φ t i m)) ≫ z i) ∧
      (∀ i, ∀ q ∈ Bk i, Set.range (q.1 ≫ pullback.fst c' (specMap A Ω)).base ⊆ Set.range (z i).base) :=
  ⟨block c' φ z hz t, card_block_le c' φ z hz t, block_nonempty c' φ z hz t,
    fun _ _ hij => disjoint_block c' φ z hz t hdisj hij,
    fun i m => ⟨_, pt_mem_block c' φ z hz t i m, pt_fst c' φ z hz t i m⟩,
    range_subset_of_mem_block c' φ z hz t⟩

def homA (i : Fin M) (m : Fin (deg i)) : B i →ₐ[A] Ω :=
  { homR φ t i m with
    commutes' := fun a => by
      have := congrArg (fun h : A →+* Ω => h a) (homR_comp_algebraMap φ t i m)
      simpa using this }

@[scoped simp] theorem homA_toRingHom (i : Fin M) (m : Fin (deg i)) : (homA φ t i m : B i →+* Ω) = homR φ t i m := rfl

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

theorem pt_eq_ptOf (i : Fin M) (m : Fin (deg i)) : pt c' φ z hz t i m = ptOf c' z hz i (homA φ t i m) := rfl

variable [∀ i, Fintype (B i →ₐ[A] Ω)]

def blockAll (i : Fin M) :
    Finset {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} := by
  classical
  exact Finset.univ.image (ptOf c' z hz i)

theorem ptOf_mem_blockAll (i : Fin M) (ψ : B i →ₐ[A] Ω) : ptOf c' z hz i ψ ∈ blockAll c' z hz i := by
  classical
  unfold blockAll
  exact Finset.mem_image_of_mem _ (Finset.mem_univ ψ)

theorem pt_mem_blockAll (i : Fin M) (m : Fin (deg i)) : pt c' φ z hz t i m ∈ blockAll c' z hz (Ω := Ω) i := by
  rw [pt_eq_ptOf]; exact ptOf_mem_blockAll c' z hz i _

theorem card_blockAll_le (hcnt : ∀ i, Fintype.card (B i →ₐ[A] Ω) ≤ deg i) (i : Fin M) :
    (blockAll c' z hz (Ω := Ω) i).card ≤ deg i := by
  classical
  unfold blockAll
  exact Finset.card_image_le.trans (by rw [Finset.card_univ]; exact hcnt i)

omit [∀ i, Fintype (B i →ₐ[A] Ω)] in
include φ t in
theorem nonempty_algHom (i : Fin M) (h : 1 ≤ deg i) : Nonempty (B i →ₐ[A] Ω) := ⟨homA φ t i ⟨0, h⟩⟩

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

end AlgebraicGeometry.WGenBlocks
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry.WGenBlocks"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec IsIntegral Spec.map Scheme Spec.map_id Scheme.Modules Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap SmoothProperCurve.specMap Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card"
namespace WDisGenus
p2m_open "AlgebraicGeometry"

section Generic

variable {R : Type u} [CommRing R] {𝒰 𝒰' : TwoChartCech.Cover.{u, u} R}
  (S : TwoChartCech.Sections.{u, u, u} 𝒰) (S' : TwoChartCech.Sections.{u, u, u} 𝒰')

theorem h0h1_of_equiv (g0 : S.M0 ≃ₗ[R] S'.M0) (g1 : S.M1 ≃ₗ[R] S'.M1) (g01 : S.M01 ≃ₗ[R] S'.M01)
    (h0 : ∀ m, S'.r0 (g0 m) = g01 (S.r0 m)) (h1 : ∀ m, S'.r1 (g1 m) = g01 (S.r1 m)) :
    Nonempty (S.H0 ≃ₗ[R] S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1) := by
  let G : (S.M0 × S.M1) ≃ₗ[R] (S'.M0 × S'.M1) := g0.prodCongr g1
  have hG : ∀ p : S.M0 × S.M1, G p = (g0 p.1, g1 p.2) := fun p => rfl
  have hd : ∀ p, S'.cechDiff (G p) = g01 (S.cechDiff p) := by
    intro p
    rw [hG, TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub, h0, h1]
  refine ⟨⟨LinearEquiv.ofSubmodules G S.H0 S'.H0 ?_⟩, ⟨Submodule.Quotient.equiv _ _ g01 ?_⟩⟩
  · ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hd, hp, map_zero]
    · intro hq
      refine ⟨G.symm q, ?_, G.apply_symm_apply q⟩
      apply g01.injective
      rw [← hd, G.apply_symm_apply, hq, map_zero]
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨G p, hd p⟩
    · rintro ⟨q, rfl⟩
      exact ⟨S.cechDiff (G.symm q), ⟨_, rfl⟩, by rw [← hd, G.apply_symm_apply]⟩

end Generic
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry.WGenBlocks"

section UnitEq

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (.of R))

noncomputable def idEquiv0 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M0 ≃ₗ[R] (𝒱.structureSheafSections x).M0 :=
  { toFun := fun m => (show Γ(X, 𝒱.U0) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U0) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

noncomputable def idEquiv1 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M1 ≃ₗ[R] (𝒱.structureSheafSections x).M1 :=
  { toFun := fun m => (show Γ(X, 𝒱.U1) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U1) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

noncomputable def idEquiv01 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01 ≃ₗ[R]
      (𝒱.structureSheafSections x).M01 :=
  { toFun := fun m => (show Γ(X, 𝒱.U0 ⊓ 𝒱.U1) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U0 ⊓ 𝒱.U1) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

theorem unit_equiv :
    Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
        (𝒱.structureSheafSections x).H0) ∧
      Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
        (𝒱.structureSheafSections x).H1) := by
  refine h0h1_of_equiv _ _ (idEquiv0 𝒱 x) (idEquiv1 𝒱 x)
    (idEquiv01 𝒱 x) ?_ ?_
  · intro m; rfl
  · intro m
    show (1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) * _ = _
    rw [one_mul]; rfl

end UnitEq
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry.WGenBlocks"

theorem finrank_baseChange_self {K : Type u} [Field K] {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (d : A →ₗ[K] B) :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank K (LinearMap.ker d) ∧
      Module.finrank K ((K ⊗[K] B) ⧸ LinearMap.range (d.baseChange K)) =
        Module.finrank K (B ⧸ LinearMap.range d) := by
  let eA := TensorProduct.lid K A
  let eB := TensorProduct.lid K B
  have hd : ∀ z, eB (d.baseChange K z) = d (eA z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [eA, eB, LinearMap.baseChange_tmul, TensorProduct.lid_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  constructor
  · refine (LinearEquiv.ofSubmodules eA (LinearMap.ker (d.baseChange K)) (LinearMap.ker d) ?_).finrank_eq
    ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hd, hp, map_zero]
    · intro hq
      refine ⟨eA.symm q, ?_, eA.apply_symm_apply q⟩
      apply eB.injective
      rw [hd, eA.apply_symm_apply, hq, map_zero]
  · refine (Submodule.Quotient.equiv _ _ eB ?_).finrank_eq
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨eA p, (hd p).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨d.baseChange K (eA.symm q), ⟨_, rfl⟩, by rw [hd, eA.apply_symm_apply]⟩

theorem rr_of_cech (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ) (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 = g) :
    (∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g) ∧
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L),
      ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by
  classical

  obtain ⟨-, ⟨eH1⟩⟩ := unit_equiv 𝒱 x
  rw [eH1.finrank_eq] at hg

  haveI : GeometricallyIntegral x := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed x
  haveI : IsIntegral (pullback x (Scheme.TwoAffineOpenCover.specMap K K)) := inferInstance
  obtain ⟨-, -, hk1⟩ := Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 x K
  obtain ⟨-, hb1⟩ := finrank_baseChange_self (𝒱.structureSheafSections x).cechDiff

  have hG : (by
      letI := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) = g := by
    rw [← hk1, hb1]
    exact hg

  have hspec : Scheme.TwoAffineOpenCover.specMap K K = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have sq : IsPullback (𝟙 X) x x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [hspec]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let eX : X ≅ pullback x (Scheme.TwoAffineOpenCover.specMap K K) := sq.isoPullback
  have heX : eX.hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = x := sq.isoPullback_hom_snd
  have heX' : eX.inv ≫ x = pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [Iso.inv_comp_eq]; exact heX.symm

  have huniq : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
    intro L _ _ M e he Kc g' hRR
    have h1 : g' = genusFF K L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
    have he2 : (e ≪≫ eX).hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = M.toBase := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [heX]; exact he
    have h2 : genusFF K L = (by
        letI := (baseToFunctionField
          (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
        exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) := by
      letI := M.functionFieldAlgebra
      letI := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K)) (e ≪≫ eX) he2
      exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)
    rw [h1, h2, hG]
  refine ⟨huniq, ?_⟩

  obtain ⟨L, _, _, M, e, he, Kc, g₀, hRR⟩ :=
    exists_curveModel_riemannRoch_of_isAlgClosed K x K (Scheme.TwoAffineOpenCover.specMap K K)
  have he' : (e ≪≫ eX.symm).hom ≫ x = M.toBase := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [heX']; exact he
  have h3 : g₀ = g := huniq L M (e ≪≫ eX.symm) he' Kc g₀ hRR
  subst h3
  exact ⟨L, inferInstance, inferInstance, M, e ≪≫ eX.symm, he', Kc, hRR⟩

end AlgebraicGeometry.WDisGenus
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry.WGenBlocks"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry.WGenBlocks"

open AlgebraicGeometry.WGenBlocks in

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b)
    (r g : ℕ) (hr : 2 * g ≤ r + 1) (hcount : r * b ^ (r - g) + (r - g) < M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i))
    [IsIntegral (pullback c (SmoothProperCurve.specMap R Ω))]
    [IsProper (pullback.snd c (SmoothProperCurve.specMap R Ω))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (SmoothProperCurve.specMap R Ω))]

    (𝒱₀ : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover)
    (hg : Module.finrank Ω (𝒱₀.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
      (𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules)).H1 = g)
    (hχ : ∀ (v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
        q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
      (𝒱 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover),
      (Module.finrank Ω (𝒱.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
          ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
            (∏ j, (v j).1.ker).module)).H0 : ℤ) -
        Module.finrank Ω (𝒱.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
          ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
            (∏ j, (v j).1.ker).module)).H1 = 1)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a : Fin (r - g) → Fin M, Function.Injective a ∧
      ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
              (∏ j, (v j).1.ker).module))).H1 := by
  classical

  obtain ⟨hg', F, _, _, Mdl, e, he, Kc, hRR⟩ :=
    AlgebraicGeometry.WDisGenus.rr_of_cech Ω (pullback.snd c (SmoothProperCurve.specMap R Ω)) g 𝒱₀ hg
  haveI : ∀ i, Fintype (B i →ₐ[R] Ω) := fun i => Fintype.ofEquiv _ (eB i).symm
  have hcnt : ∀ i, Fintype.card (B i →ₐ[R] Ω) ≤ deg i := fun i => by
    rw [Fintype.card_congr (eB i), Fintype.card_fin]
  have hne : ∀ i, Nonempty (B i →ₐ[R] Ω) := fun i => ⟨(eB i).symm ⟨0, hdeg i⟩⟩

  have hz' : ∀ i, z i ≫ c = SmoothProperCurve.specMap R (B i) := hz
  have hM : 0 < M := by omega
  have hb1 : 1 ≤ b := (hdeg ⟨0, hM⟩).trans (hdegb ⟨0, hM⟩)
  obtain ⟨a, ha, H⟩ :=
    AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card
      Ω (pullback.snd c (SmoothProperCurve.specMap R Ω)) g hg' Mdl e he Kc hRR
      (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).2
      L₀ hL₀ h0 r hr (ι := ULift.{u} (Fin M))
      (fun i => blockAll c z hz' (Ω := Ω) i.down)
      (fun i i' h => disjoint_blockAll c z hz' hzdisj (fun hh => h (ULift.ext i i' hh)))
      hb1 (fun i => (card_blockAll_le c z hz' hcnt i.down).trans (hdegb i.down))
      (by rw [Fintype.card_ulift, Fintype.card_fin]; exact hcount) hχ

  refine ⟨fun j => (a j).down, ULift.down_injective.comp ha, fun v hv 𝒲 => H v (fun j => ?_) 𝒲⟩

  obtain ⟨ψ, hψ⟩ := hv j
  have hvj : v j = ptOf c z hz' (a j).down ψ := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [hψ, ptOf_fst]
    · rw [(v j).2, (ptOf c z hz' (a j).down ψ).2]
  rw [hvj]
  exact ptOf_mem_blockAll c z hz' (a j).down ψ

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.AlgebraicGeometry.WGenBlocks"

end S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre (solution)
