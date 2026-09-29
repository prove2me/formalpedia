-- Prove2me | solution 1 for AlgebraicCurve.le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b781662d-f21f-520e-b4d1-44b43ed31be4

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_exists_forall_ord_residue_smul_eq_zero_of_forall_degree_eq_zero_of_semistableCovering
import Theorems.Thm_AlgebraicCurve_SemistableCovering_sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ToricCountSol

section Graph

variable {n m : ℕ} (src tgt : Fin m → Fin n)

def CutConnected : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S)

variable {src tgt}

theorem CutConnected.const (h : CutConnected src tgt) {X : Type*} (φ : Fin n → X)
    (hφ : ∀ e, φ (src e) = φ (tgt e)) : ∀ i j, φ i = φ j := by
  classical
  intro i j
  set S : Finset (Fin n) := Finset.univ.filter fun l => φ l = φ i with hS
  have hi : i ∈ S := by simp [hS]
  by_contra hne
  have hj : j ∈ Sᶜ := by
    rw [Finset.mem_compl]
    intro hj
    apply hne
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj.symm
  obtain ⟨e, he⟩ := h S ⟨i, hi⟩ ⟨j, hj⟩
  have h1 : src e ∈ S ↔ tgt e ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, hφ e]
  rw [h1] at he
  by_cases ht : tgt e ∈ S
  · exact (he.mp ht) ht
  · exact ht (he.mpr ht)

theorem CutConnected.le_add_one (h : CutConnected src tgt) : n ≤ m + 1 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let δ : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ) :=
    { toFun := fun φ e => φ (tgt e) - φ (src e)
      map_add' := fun φ ψ => by ext e; simp only [Pi.add_apply]; ring
      map_smul' := fun r φ => by ext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

  let ev : LinearMap.ker δ →ₗ[ℚ] ℚ :=
    { toFun := fun φ => (φ : Fin n → ℚ) i₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro φ ψ hφψ
    apply Subtype.ext
    have hφ : δ (φ : Fin n → ℚ) = 0 := φ.2
    have hψ : δ (ψ : Fin n → ℚ) = 0 := ψ.2
    have hc : ∀ e, ((φ : Fin n → ℚ) - (ψ : Fin n → ℚ)) (src e) = ((φ : Fin n → ℚ) - (ψ : Fin n → ℚ)) (tgt e) := by
      intro e
      have h1 := congrFun hφ e
      have h2 := congrFun hψ e
      simp only [δ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1 h2
      simp only [Pi.sub_apply]
      linarith
    have hall := h.const _ hc
    funext l
    have := hall l i₀
    simp only [Pi.sub_apply] at this
    have h0 : (φ : Fin n → ℚ) i₀ = (ψ : Fin n → ℚ) i₀ := hφψ
    linarith
  have hker : Module.finrank ℚ (LinearMap.ker δ) ≤ 1 := by
    have := LinearMap.finrank_le_finrank_of_injective hev
    simpa using this
  have hrange : Module.finrank ℚ (LinearMap.range δ) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range δ)
    rwa [Module.finrank_fin_fun] at this
  have hsum := LinearMap.finrank_range_add_finrank_ker δ
  rw [Module.finrank_fin_fun] at hsum
  omega

end Graph

section Coboundary

variable {n m : ℕ} (src tgt : Fin m → Fin n) (R : Type*) [CommGroup R]

def cobd : (Fin n → R) →* (Fin m → R) where
  toFun ν e := ν (src e) / ν (tgt e)
  map_one' := by ext e; simp
  map_mul' ν ν' := by ext e; simp only [Pi.mul_apply]; rw [mul_div_mul_comm]

@[scoped simp] theorem cobd_apply (ν : Fin n → R) (e : Fin m) : cobd src tgt R ν e = ν (src e) / ν (tgt e) := rfl

variable {src tgt R}

theorem card_quotient_mul (h : CutConnected src tgt) [Finite R] (hn : 0 < n) :
    Nat.card ((Fin m → R) ⧸ (cobd src tgt R).range) * Nat.card R ^ n = Nat.card R ^ (m + 1) := by
  classical
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set δ := cobd src tgt R with hδ

  have h1 : Nat.card (Fin m → R) = Nat.card ((Fin m → R) ⧸ δ.range) * Nat.card δ.range :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _

  have h2 : Nat.card (Fin n → R) = Nat.card δ.range * Nat.card δ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv]

  have h3 : Nat.card δ.ker = Nat.card R := by
    refine Nat.card_congr (Equiv.ofBijective (fun ν : δ.ker => (ν : Fin n → R) i₀) ⟨?_, ?_⟩)
    · intro ν ν' hνν'
      apply Subtype.ext
      have hν : δ (ν : Fin n → R) = 1 := ν.2
      have hν' : δ (ν' : Fin n → R) = 1 := ν'.2
      have hc : ∀ e, ((ν : Fin n → R) / (ν' : Fin n → R)) (src e) = ((ν : Fin n → R) / (ν' : Fin n → R)) (tgt e) := by
        intro e
        have a := congrFun hν e
        have b := congrFun hν' e
        simp only [hδ, cobd_apply, Pi.one_apply, div_eq_one] at a b
        simp only [Pi.div_apply, a, b]
      have hall := h.const _ hc
      funext l
      have := hall l i₀
      simp only [Pi.div_apply] at this
      have h0 : (ν : Fin n → R) i₀ = (ν' : Fin n → R) i₀ := hνν'
      rw [h0, div_self'] at this
      exact div_eq_one.mp this
    · intro r
      refine ⟨⟨fun _ => r, ?_⟩, rfl⟩
      show δ (fun _ => r) = 1
      ext e
      simp [hδ]
  rw [Nat.card_fun, Nat.card_fin] at h1 h2
  rw [h3] at h2
  calc Nat.card ((Fin m → R) ⧸ δ.range) * Nat.card R ^ n
      = Nat.card ((Fin m → R) ⧸ δ.range) * (Nat.card δ.range * Nat.card R) := by rw [h2]
    _ = (Nat.card ((Fin m → R) ⧸ δ.range) * Nat.card δ.range) * Nat.card R := by ring
    _ = Nat.card R ^ m * Nat.card R := by rw [← h1]
    _ = Nat.card R ^ (m + 1) := by rw [pow_succ]

theorem card_quotient_le (h : CutConnected src tgt) [Finite R] (K : ℕ) (hK : Nat.card R ≤ K) (hK1 : 1 ≤ K) :
    Nat.card ((Fin m → R) ⧸ (cobd src tgt R).range) ≤ K ^ (m + 1 - n) := by
  classical
  have hR : 0 < Nat.card R := Nat.card_pos
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    calc Nat.card ((Fin m → R) ⧸ (cobd src tgt R).range)
        ≤ Nat.card (Fin m → R) := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (cobd src tgt R).range]
          exact Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card R ^ m := by
          rw [Nat.card_fun, Nat.card_fin]
      _ ≤ K ^ m := Nat.pow_le_pow_left hK m
      _ ≤ K ^ (m + 1 - 0) := Nat.pow_le_pow_right hK1 (by omega)
  · have hnm : n ≤ m + 1 := h.le_add_one
    have key := card_quotient_mul (R := R) h hn
    have hsplit : Nat.card R ^ (m + 1) = Nat.card R ^ (m + 1 - n) * Nat.card R ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hnm]
    rw [hsplit] at key
    have hcancel := Nat.eq_of_mul_eq_mul_right (pow_pos hR n) key
    rw [hcancel]
    exact Nat.pow_le_pow_left hK _

end Coboundary

section Util

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem ord_const_smul (v : Place K E) {c : K} (hc : c ≠ 0) {f : E} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero (algebraMap K E)).mpr hc) hf,
    AlgebraicCurve.Place.ord_algebraMap, zero_add]

theorem ord_pow (v : Place K E) (f : E) (k : ℕ) : v.ord (f ^ k) = (k : ℤ) * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem mem_of_ord_eq_zero (v : Place K E) {f : E} (hf : f ≠ 0) (h : v.ord f = 0) :
    f ∈ v.toValuationSubring :=
  (AlgebraicCurve.Place.mem_iff_ord_nonneg v hf).mpr h.ge

theorem evalAt_pow (v : Place K E) (hv : v.IsRational) {f : E} (hf : f ∈ v.toValuationSubring) (k : ℕ) :
    v.evalAt (f ^ k) = v.evalAt f ^ k := by
  induction k with
  | zero => simp [AlgebraicCurve.Place.evalAt_one]
  | succ k ih =>
      rw [pow_succ, AlgebraicCurve.Place.evalAt_mul v hv (pow_mem hf k) hf, ih, pow_succ]

theorem evalAt_mul_inv_mul_inv (v : Place K E) (hv : v.IsRational) {f g : E} (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hf : v.ord f = 0) (hg : v.ord g = 0) {c : K} (hc : c ≠ 0) :
    v.evalAt (f * g⁻¹ * (algebraMap K E c)⁻¹) = v.evalAt f * (v.evalAt g)⁻¹ * c⁻¹ := by
  have hfm := mem_of_ord_eq_zero v hf0 hf
  have hgm : g⁻¹ ∈ v.toValuationSubring :=
    mem_of_ord_eq_zero v (inv_ne_zero hg0) (by rw [v.ord_inv, hg, neg_zero])
  have hcm : (algebraMap K E c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' _
  rw [AlgebraicCurve.Place.evalAt_mul v hv (mul_mem hfm hgm) hcm,
    AlgebraicCurve.Place.evalAt_mul v hv hfm hgm, AlgebraicCurve.Place.evalAt_inv v hv hg0 hg, ← map_inv₀,
    AlgebraicCurve.Place.evalAt_algebraMap]

theorem mapDomain_apply_eq_zero_of_forall_ne {α β : Type*} (φ : α → β) (D : α →₀ ℤ) (b : β)
    (h : ∀ a ∈ D.support, φ a ≠ b) : Finsupp.mapDomain φ D b = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    show (Finsupp.single (φ a) (D a)) b = 0
    rw [Finsupp.single_apply, if_neg (h a ha)]

end Util

section ChartUtil

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem residue_ne_zero_imp_ne_zero (C : ComponentChart A F Fb) {c : L} {f : F}
    (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hc0
  have h0 : (⟨(0 : L) • f, hc⟩ : C.integers) = 0 := Subtype.ext (zero_smul L f)
  rw [h0, map_zero]

theorem ne_zero_of_residue_ne_zero (C : ComponentChart A F Fb) {f : F}
    (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hres
  have h0 : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
  rw [h0, map_zero]

theorem unit_smul (C : ComponentChart A F Fb) {u : L} (huA : u ∈ A) (hu : IsUnit (⟨u, huA⟩ : A))
    {x : F} (hx : x ∈ C.integers) :
    ∃ h : u • x ∈ C.integers, C.residue ⟨u • x, h⟩ =
      algebraMap (ResidueField A) Fb (residue A ⟨u, huA⟩) * C.residue ⟨x, hx⟩ ∧
      algebraMap (ResidueField A) Fb (residue A ⟨u, huA⟩) ≠ 0 := by
  have hum : algebraMap L F u ∈ C.integers := (C.algebraMap_mem_iff u).mpr huA
  have hmem : u • x ∈ C.integers := by rw [Algebra.smul_def]; exact mul_mem hum hx
  refine ⟨hmem, ?_, ?_⟩
  · have hprod : (⟨u • x, hmem⟩ : C.integers) = ⟨algebraMap L F u, hum⟩ * ⟨x, hx⟩ :=
      Subtype.ext (Algebra.smul_def u x)
    rw [hprod, map_mul]
    congr 1
    exact C.residue_algebraMap ⟨u, huA⟩
  · rw [map_ne_zero_iff _ (algebraMap (ResidueField A) Fb).injective, Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm hu

end ChartUtil

section Covering

theorem sum_apply_of_mem_dom {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {n m : ℕ} {Fbar : Fin n → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (Di : Fin n → Divisor L F) (hsupp : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    {i : Fin n} {P : Place L F} (hP : P ∈ (C i).dom) : (∑ j, Di j) P = Di i P := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    by_contra h
    have hPj : P ∈ (C j).dom := hsupp j P (Finsupp.mem_support_iff.mpr h)
    rcases hcover P with ⟨i', -, huniq, -⟩ | ⟨e, -, -, hno⟩
    · exact hji ((huniq j hPj).trans (huniq i hP).symm)
    · exact hno i hP
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_apply_of_mem_annulus {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {n m : ℕ} {Fbar : Fin n → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (Di : Fin n → Divisor L F) (hsupp : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    {e : Fin m} {P : Place L F} (hP : P ∈ (An e).dom) : (∑ j, Di j) P = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_contra h
  have hPj : P ∈ (C j).dom := hsupp j P (Finsupp.mem_support_iff.mpr h)
  rcases hcover P with ⟨i', -, -, hno⟩ | ⟨e', -, -, hno⟩
  · exact hno e hP
  · exact hno j hPj

theorem apply_eq_zero_of_not_mem {α : Type*} (D : α →₀ ℤ) {S : Set α} (hsupp : ∀ P ∈ D.support, P ∈ S)
    {P : α} (hP : P ∉ S) : D P = 0 := by
  by_contra h
  exact hP (hsupp P (Finsupp.mem_support_iff.mpr h))

theorem zsmul_mem_principal_of_zsmul_mk_eq_zero {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (k : ℤ)
    (h : k • Pic0.mk ⟨D, hD⟩ = 0) : k • D ∈ Divisor.principal (K := L) (F := F) := by
  have h1 : (QuotientAddGroup.mk (k • (⟨D, hD⟩ : Divisor.degZero (K := L) (F := F))) : Pic0 L F) = 0 := by
    rw [QuotientAddGroup.mk_zsmul]; exact h
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
  exact h1

theorem mk_eq_mk_of_sub_mem_principal {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (D D' : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (hD' : D' ∈ Divisor.degZero (K := L) (F := F))
    (h : D' - D ∈ Divisor.principal (K := L) (F := F)) : Pic0.mk ⟨D, hD⟩ = Pic0.mk ⟨D', hD'⟩ := by
  symm
  show (QuotientAddGroup.mk (⟨D', hD'⟩ : Divisor.degZero (K := L) (F := F)) : Pic0 L F) =
    QuotientAddGroup.mk (⟨D, hD⟩ : Divisor.degZero (K := L) (F := F))
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : ((-(⟨D', hD'⟩ : Divisor.degZero (K := L) (F := F)) + ⟨D, hD⟩ :
      Divisor.degZero (K := L) (F := F)) : Divisor L F) = -(D' - D) := by
    push_cast; abel
  rw [this]
  exact neg_mem h

theorem exists_normalized
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (hconn : CutConnected src tgt)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A)) (hk0 : 0 < k)
    (c : Pic0 L F) (hkc : (k : ℤ) • c = 0)
    (htor : ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
      Pic0.mk ⟨D, hD⟩ = c ∧ D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
      (∀ i, Divisor.degree (Di i) = 0) ∧
      ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
        Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i)) :
    ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F)
      (g : ∀ i, Fbar i),
      Pic0.mk ⟨D, hD⟩ = c ∧ D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
      (∀ i, g i ≠ 0) ∧
      (∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i),
        Finsupp.mapDomain (C i).placeMap (Di i) Q = Q.ord (g i)) ∧
      ∀ e, (xs e).evalAt (g (src e)) ≠ 0 ∧ (xt e).evalAt (g (tgt e)) ≠ 0 ∧
        ((xs e).evalAt (g (src e)) / (xt e).evalAt (g (tgt e))) ^ k = 1 := by
  classical
  obtain ⟨D, hD, Di, hc, hsum, hsupp, hdeg, hprin⟩ := htor
  choose g hg0 hg using fun i => (Divisor.mem_principal.mp (hprin i))

  have hnode_g : ∀ i, ∀ x ∈ (C i).nodes, x.ord (g i) = 0 := by
    intro i x hx
    rw [← hg i x]
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun P hP h => ?_
    exact (C i).placeMap_not_mem_nodes P (hsupp i P hP) (h ▸ hx)
  rcases Nat.eq_zero_or_pos n with hn | hn
  ·
    refine ⟨D, hD, Di, g, hc, hsum, hsupp, hg0, hg, fun e => ?_⟩
    exact absurd (src e).isLt (by omega)
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  obtain ⟨f, hf0, hf⟩ : ∃ f : F, f ≠ 0 ∧ ∀ P, ((k : ℤ) • D) P = P.ord f :=
    Divisor.mem_principal.mp (zsmul_mem_principal_of_zsmul_mk_eq_zero D hD k (hc ▸ hkc))
  have hford : ∀ e, ∀ P ∈ (An e).dom, P.ord f = 0 := by
    intro e P hP
    rw [← hf P, Finsupp.smul_apply, hsum, sum_apply_of_mem_annulus C An hcover Di hsupp hP, smul_zero]
  have hE : ∀ i, ∀ P ∈ (C i).dom, ((k : ℤ) • Di i) P = P.ord f := by
    intro i P hP
    rw [← hf P, Finsupp.smul_apply, Finsupp.smul_apply, hsum, sum_apply_of_mem_dom C An hcover Di hsupp hP]
  have hE' : ∀ i, ∀ P, P ∉ (C i).dom → ((k : ℤ) • Di i) P = 0 := by
    intro i P hP
    rw [Finsupp.smul_apply, apply_eq_zero_of_not_mem (Di i) (hsupp i) hP, smul_zero]
  have hdegE : ∀ i, Divisor.degree ((k : ℤ) • Di i) = 0 := by
    intro i; rw [map_zsmul, hdeg i, smul_zero]

  obtain ⟨c₀, hc₀0, hunit, hval, -⟩ :=
    AlgebraicCurve.exists_forall_ord_residue_smul_eq_zero_of_forall_degree_eq_zero_of_semistableCovering
      A π hπ hπ0 F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes f hf0 hford
      (fun i => (k : ℤ) • Di i) hE hE' hdegE

  set a : L := c₀ i₀ with ha
  have ha0 : a ≠ 0 := hc₀0 i₀
  have hva : ∀ i, A.valuation (c₀ i) = A.valuation a :=
    fun i => hconn.const (fun i => A.valuation (c₀ i)) hval i i₀
  have haf : ∀ i, ∃ h : a • f ∈ (C i).integers, (C i).residue ⟨a • f, h⟩ ≠ 0 ∧
      ∀ x ∈ (C i).nodes, x.ord ((C i).residue ⟨a • f, h⟩) = 0 := by
    intro i
    obtain ⟨h1, hres, hnodes0⟩ := hunit i
    set u : L := a / c₀ i with hu
    have hu1 : A.valuation u = 1 := by
      rw [hu, map_div₀, hva i, div_self]
      exact (Valuation.ne_zero_iff _).mpr ha0
    have huA : u ∈ A := A.mem_of_valuation_le_one _ hu1.le
    have huunit : IsUnit (⟨u, huA⟩ : A) := (ValuationSubring.valuation_eq_one_iff A _).mpr hu1
    obtain ⟨hmem, hres_eq, hr0⟩ := unit_smul (C i) huA huunit h1
    have hau : a • f = u • (c₀ i • f) := by
      rw [smul_smul, hu, div_mul_cancel₀ _ (hc₀0 i)]
    have hmem' : a • f ∈ (C i).integers := by rw [hau]; exact hmem
    have hres' : (C i).residue ⟨a • f, hmem'⟩ =
        algebraMap (ResidueField A) (Fbar i) (residue A ⟨u, huA⟩) * (C i).residue ⟨c₀ i • f, h1⟩ := by
      rw [← hres_eq]; congr 1; exact Subtype.ext hau
    refine ⟨hmem', ?_, fun x hx => ?_⟩
    · rw [hres']; exact mul_ne_zero hr0 hres
    · rw [hres', x.ord_mul hr0 hres, AlgebraicCurve.Place.ord_algebraMap, hnodes0 x hx, zero_add]
  choose haI hres hnode using haf
  set fb : ∀ i, Fbar i := fun i => (C i).residue ⟨a • f, haI i⟩ with hfb
  have hfb0 : ∀ i, fb i ≠ 0 := hres

  have hreg : ∀ e, ∀ P ∈ (An e).dom, 0 ≤ P.ord (a • f) := fun e P hP => by
    rw [ord_const_smul P ha0 hf0, hford e P hP]
  have hev : ∀ e, (xs e).evalAt (fb (src e)) = (xt e).evalAt (fb (tgt e)) := fun e =>
    (AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached A (An e) (An' e)
      (hpair e).1 (hpair e).2.1 (hpair e).2.2.1 (hpair e).2.2.2 (C (src e)) (xs e) (hratBar _ _) (hatt e).1
      (C (tgt e)) (xt e) (hratBar _ _) (hatt e).2 (a • f) (haI (src e)) (haI (tgt e)) (hreg e)).2.2

  have hordfb : ∀ i, ∀ Q : Place (ResidueField A) (Fbar i), Q.ord (fb i) = (k : ℤ) * Q.ord (g i) := by
    intro i Q
    by_cases hQ : Q ∈ (C i).nodes
    · rw [hnode i Q hQ, hnode_g i Q hQ, mul_zero]
    · have h := (C i).mapDomain_placeMap ⟨a • f, haI i⟩ (hres i) ((k : ℤ) • Di i)
        (fun P hP => by rw [hE i P hP, ord_const_smul P ha0 hf0]) (hE' i) Q hQ
      rw [Finsupp.mapDomain_smul, Finsupp.smul_apply, hg i Q, smul_eq_mul] at h
      exact h.symm

  have hconst : ∀ i, ∃ b : ResidueField A, b ≠ 0 ∧
      fb i = (algebraMap (ResidueField A) (Fbar i) b * g i) ^ k := by
    intro i
    set r : Fbar i := fb i * ((g i) ^ k)⁻¹ with hr
    have hgk0 : (g i) ^ k ≠ 0 := pow_ne_zero _ (hg0 i)
    have hr0 : r ≠ 0 := mul_ne_zero (hfb0 i) (inv_ne_zero hgk0)
    have hordr : ∀ Q : Place (ResidueField A) (Fbar i), Q.ord r = 0 := by
      intro Q
      rw [hr, Q.ord_mul (hfb0 i) (inv_ne_zero hgk0), Q.ord_inv, ord_pow, hordfb i Q]
      ring
    obtain ⟨t, ht, hfin, -⟩ :=
      (IsCurveOver.exists_separating_transcendental (K := ResidueField A) (F := Fbar i))
    haveI := hfin
    obtain ⟨a₁, ha₁⟩ := AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t ht hordr
    have ha₁0 : a₁ ≠ 0 := by
      rintro rfl; rw [map_zero] at ha₁; exact hr0 ha₁.symm
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a₁ hk0
    have hb0 : b ≠ 0 := by rintro rfl; rw [zero_pow hk0.ne'] at hb; exact ha₁0 hb.symm
    refine ⟨b, hb0, ?_⟩
    rw [mul_pow, ← map_pow, hb, ha₁, hr, inv_mul_cancel_right₀ hgk0]
  choose b hb0 hb using hconst
  set g' : ∀ i, Fbar i := fun i => algebraMap (ResidueField A) (Fbar i) (b i) * g i with hg'
  have hg'0 : ∀ i, g' i ≠ 0 := fun i => mul_ne_zero ((map_ne_zero _).mpr (hb0 i)) (hg0 i)
  have hordg' : ∀ i, ∀ Q : Place (ResidueField A) (Fbar i), Q.ord (g' i) = Q.ord (g i) := by
    intro i Q
    rw [hg', Q.ord_mul ((map_ne_zero _).mpr (hb0 i)) (hg0 i), AlgebraicCurve.Place.ord_algebraMap, zero_add]
  have hfbg' : ∀ i, fb i = (g' i) ^ k := hb
  refine ⟨D, hD, Di, g', hc, hsum, hsupp, hg'0, fun i Q => by rw [hordg', hg], fun e => ?_⟩

  have hs0 : (xs e).ord (g' (src e)) = 0 := by rw [hordg', hnode_g _ _ (hatt e).1.1]
  have ht0 : (xt e).ord (g' (tgt e)) = 0 := by rw [hordg', hnode_g _ _ (hatt e).2.1]
  have hsm := mem_of_ord_eq_zero _ (hg'0 _) hs0
  have htm := mem_of_ord_eq_zero _ (hg'0 _) ht0
  have hse : (xs e).evalAt (g' (src e)) ≠ 0 :=
    AlgebraicCurve.Place.evalAt_ne_zero _ (hratBar _ _) (hg'0 _) hs0
  have hte : (xt e).evalAt (g' (tgt e)) ≠ 0 :=
    AlgebraicCurve.Place.evalAt_ne_zero _ (hratBar _ _) (hg'0 _) ht0
  have hfbt0 : (xt e).evalAt (fb (tgt e)) ≠ 0 := by
    rw [hfbg', evalAt_pow _ (hratBar _ _) htm]; exact pow_ne_zero _ hte
  refine ⟨hse, hte, ?_⟩
  rw [div_pow, ← evalAt_pow _ (hratBar _ _) hsm, ← evalAt_pow _ (hratBar _ _) htm, ← hfbg', ← hfbg', hev e,
    div_self hfbt0]

end Covering

theorem mapDomain_sub' {α β : Type*} (φ : α → β) (a b : α →₀ ℤ) :
    Finsupp.mapDomain φ (a - b) = Finsupp.mapDomain φ a - Finsupp.mapDomain φ b :=
  map_sub (Finsupp.mapDomain.addMonoidHom φ) a b

theorem eq_of_periods
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (Mdl : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (Dsc : Mdl.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (c c' : Pic0 L F) (hkc : (k : ℤ) • c = 0) (hkc' : (k : ℤ) • c' = 0)
    (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F)
    (g : ∀ i, Fbar i) (hc : Pic0.mk ⟨D, hD⟩ = c) (hsum : D = ∑ i, Di i)
    (hsupp : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) (hg0 : ∀ i, g i ≠ 0)
    (hg : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i),
      Finsupp.mapDomain (C i).placeMap (Di i) Q = Q.ord (g i))
    (D' : Divisor L F) (hD' : D' ∈ Divisor.degZero (K := L) (F := F)) (Di' : Fin n → Divisor L F)
    (g' : ∀ i, Fbar i) (hc' : Pic0.mk ⟨D', hD'⟩ = c') (hsum' : D' = ∑ i, Di' i)
    (hsupp' : ∀ i, ∀ P ∈ (Di' i).support, P ∈ (C i).dom) (hg'0 : ∀ i, g' i ≠ 0)
    (hg' : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i),
      Finsupp.mapDomain (C i).placeMap (Di' i) Q = Q.ord (g' i))
    (ν : Fin n → IsLocalRing.ResidueField A) (hν0 : ∀ i, ν i ≠ 0)
    (hrel : ∀ e, (xs e).evalAt (g' (src e)) / (xt e).evalAt (g' (tgt e)) =
      (xs e).evalAt (g (src e)) / (xt e).evalAt (g (tgt e)) * (ν (src e) / ν (tgt e))) :
    c = c' := by
  classical

  have hnode : ∀ (Dj : Fin n → Divisor L F) (hs : ∀ i, ∀ P ∈ (Dj i).support, P ∈ (C i).dom)
      (h : ∀ i, Fbar i) (hh : ∀ i, ∀ Q, Finsupp.mapDomain (C i).placeMap (Dj i) Q = Q.ord (h i))
      (i : Fin n), ∀ x ∈ (C i).nodes, x.ord (h i) = 0 := by
    intro Dj hs h hh i x hx
    rw [← hh i x]
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun P hP h => ?_
    exact (C i).placeMap_not_mem_nodes P (hs i P hP) (h ▸ hx)
  set G : ∀ i, Fbar i := fun i =>
    g' i * (g i)⁻¹ * (algebraMap (IsLocalRing.ResidueField A) (Fbar i) (ν i))⁻¹ with hG
  have hG0 : ∀ i, G i ≠ 0 := fun i =>
    mul_ne_zero (mul_ne_zero (hg'0 i) (inv_ne_zero (hg0 i))) (inv_ne_zero ((map_ne_zero _).mpr (hν0 i)))
  have key :=
    AlgebraicCurve.SemistableCovering.sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus Mdl Dsc
      (fun i => Di' i - Di i) (fun i P hP => ?_) G hG0 (fun i Q => ?_) (fun e => ?_) k hk ?_
  ·
    have hsub : (∑ i, (Di' i - Di i)) = D' - D := by rw [Finset.sum_sub_distrib, ← hsum, ← hsum']
    rw [hsub] at key
    rw [← hc, ← hc']
    exact mk_eq_mk_of_sub_mem_principal D D' hD hD' key
  ·
    have h := Finsupp.mem_support_iff.mp hP
    rw [Finsupp.sub_apply] at h
    by_cases h1 : Di' i P = 0
    · rw [h1, zero_sub, neg_ne_zero] at h
      exact hsupp i P (Finsupp.mem_support_iff.mpr h)
    · exact hsupp' i P (Finsupp.mem_support_iff.mpr h1)
  ·
    rw [mapDomain_sub', Finsupp.sub_apply, hg i Q, hg' i Q, hG]
    rw [Q.ord_mul (mul_ne_zero (hg'0 i) (inv_ne_zero (hg0 i))) (inv_ne_zero ((map_ne_zero _).mpr (hν0 i))),
      Q.ord_mul (hg'0 i) (inv_ne_zero (hg0 i)), Q.ord_inv, Q.ord_inv, AlgebraicCurve.Place.ord_algebraMap]
    ring
  ·
    have hs := hnode Di hsupp g hg _ _ (hatt e).1.1
    have ht := hnode Di hsupp g hg _ _ (hatt e).2.1
    have hs' := hnode Di' hsupp' g' hg' _ _ (hatt e).1.1
    have ht' := hnode Di' hsupp' g' hg' _ _ (hatt e).2.1
    have es0 := AlgebraicCurve.Place.evalAt_ne_zero _ (hratBar _ (xs e)) (hg0 _) hs
    have et0 := AlgebraicCurve.Place.evalAt_ne_zero _ (hratBar _ (xt e)) (hg0 _) ht
    have es0' := AlgebraicCurve.Place.evalAt_ne_zero _ (hratBar _ (xs e)) (hg'0 _) hs'
    have et0' := AlgebraicCurve.Place.evalAt_ne_zero _ (hratBar _ (xt e)) (hg'0 _) ht'
    rw [hG]
    rw [evalAt_mul_inv_mul_inv _ (hratBar _ _) (hg'0 _) (hg0 _) hs' hs (hν0 _),
      evalAt_mul_inv_mul_inv _ (hratBar _ _) (hg'0 _) (hg0 _) ht' ht (hν0 _)]
    have h := hrel e
    have hνs := hν0 (src e)
    have hνt := hν0 (tgt e)
    field_simp at h
    field_simp
    linear_combination h
  ·
    have hsub : (∑ i, (Di' i - Di i)) = D' - D := by rw [Finset.sum_sub_distrib, ← hsum, ← hsum']
    rw [hsub, smul_sub]
    exact sub_mem (zsmul_mem_principal_of_zsmul_mk_eq_zero D' hD' k (hc' ▸ hkc'))
      (zsmul_mem_principal_of_zsmul_mk_eq_zero D hD k (hc ▸ hkc))

end ToricCountSol
p2m_reactivate "P2MW.S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.ToricCountSol"

set_option maxHeartbeats 4000000 in
open ToricCountSol in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (Mdl : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (Dsc : Mdl.Descent)
    :
    n ≤ m + 1 ∧
    ∀ k : ℕ, IsUnit ((k : ℕ) : IsLocalRing.ResidueField A) →
      ∃ B : Finset (Pic0 L F), B.card ≤ k ^ (m + 1 - n) ∧
        ∀ c : Pic0 L F, (k : ℤ) • c = 0 →
          (∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
            Pic0.mk ⟨D, hD⟩ = c ∧ D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
            (∀ i, Divisor.degree (Di i) = 0) ∧
            ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
              Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i)) →
          c ∈ B := by
  classical
  have hconn : CutConnected src tgt :=
    AlgebraicCurve.SemistableCovering.exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus
  refine ⟨hconn.le_add_one, fun k hk => ?_⟩
  have hk0 : 0 < k := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    rw [Nat.cast_zero] at hk
    exact not_isUnit_zero hk
  haveI : NeZero k := ⟨hk0.ne'⟩

  let R : Type := ↥(rootsOfUnity k (IsLocalRing.ResidueField A))
  have hRk : Nat.card R ≤ k := card_rootsOfUnity (IsLocalRing.ResidueField A) k
  haveI : Finite ((Fin m → R) ⧸ (cobd src tgt R).range) := inferInstance

  let T : Set (Pic0 L F) := {c | (k : ℤ) • c = 0 ∧
    ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
      Pic0.mk ⟨D, hD⟩ = c ∧ D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
      (∀ i, Divisor.degree (Di i) = 0) ∧
      ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
        Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i)}
  have hN : ∀ c : T, _ := fun c =>
    exists_normalized A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes
      hcover hdisc hgenus hconn k hk hk0 c.1 c.2.1 c.2.2
  choose Dc hDc Dic gc hcc hsumc hsuppc hgc0 hgc hperc using hN

  let ζ : T → (Fin m → R) := fun c e =>
    ⟨Units.mk0 ((xs e).evalAt (gc c (src e)) / (xt e).evalAt (gc c (tgt e)))
        (div_ne_zero (hperc c e).1 (hperc c e).2.1),
      (mem_rootsOfUnity' k _).mpr (by rw [Units.val_mk0]; exact (hperc c e).2.2)⟩
  have hζ : ∀ (c : T) (e : Fin m), (((ζ c e : R) : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
      (xs e).evalAt (gc c (src e)) / (xt e).evalAt (gc c (tgt e)) := fun c e => rfl
  let Ψ : T → (Fin m → R) ⧸ (cobd src tgt R).range := fun c => QuotientGroup.mk (ζ c)
  have hΨ : Function.Injective Ψ := by
    intro c c' h
    obtain ⟨ν, hν⟩ := MonoidHom.mem_range.mp (QuotientGroup.eq.mp h)
    apply Subtype.ext
    refine eq_of_periods A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes
      hcover hdisc hgenus Mdl Dsc k hk c.1 c'.1 c.2.1 c'.2.1 (Dc c) (hDc c) (Dic c) (gc c) (hcc c) (hsumc c) (hsuppc c)
      (hgc0 c) (hgc c) (Dc c') (hDc c') (Dic c') (gc c') (hcc c') (hsumc c') (hsuppc c') (hgc0 c') (hgc c')
      (fun i => (((ν i : R) : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
      (fun i => Units.ne_zero _) (fun e => ?_)
    beta_reduce
    have h1 := congrFun hν e
    simp only [cobd_apply, Pi.mul_apply, Pi.inv_apply] at h1
    have h2 : ν (src e) = (ζ c e)⁻¹ * ζ c' e * ν (tgt e) := div_eq_iff_eq_mul.mp h1
    have h0 : ζ c e * ν (src e) = ζ c' e * ν (tgt e) := by
      rw [h2, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have h3 := congrArg
      (fun r : R => ((r : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A)) h0
    have h4 : (xs e).evalAt (gc c (src e)) / (xt e).evalAt (gc c (tgt e)) *
        (((ν (src e) : R) : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
        (xs e).evalAt (gc c' (src e)) / (xt e).evalAt (gc c' (tgt e)) *
        (((ν (tgt e) : R) : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := h3
    have hνt : (((ν (tgt e) : R) : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) ≠ 0 :=
      Units.ne_zero _
    rw [← mul_div_assoc, eq_div_iff hνt]
    exact h4.symm
  haveI hTfin : Finite T := Finite.of_injective Ψ hΨ
  have hcard : Nat.card T ≤ k ^ (m + 1 - n) :=
    (Nat.card_le_card_of_injective Ψ hΨ).trans (card_quotient_le (R := R) hconn k hRk hk0)
  have hTf : T.Finite := Set.toFinite T
  refine ⟨hTf.toFinset, ?_, fun c hkc htor => (Set.Finite.mem_toFinset hTf).mpr ⟨hkc, htor⟩⟩
  rw [← Set.ncard_eq_toFinset_card T hTf, ← Nat.card_coe_set_eq]
  exact hcard

end
p2m_reactivate "P2MW.S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.ToricCountSol"

end S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel (solution)
