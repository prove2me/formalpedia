-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/68b17eb1-7cf2-5485-abfd-dbe96c0753ae

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne
import Theorems.Thm_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace InjSol

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_const_smul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero (algebraMap K F)).mpr hc) hf,
    AlgebraicCurve.Place.ord_algebraMap, zero_add]

theorem degree_eq_finsuppDegree (D : Divisor K F) (h : ∀ P ∈ D.support, Place.IsRational P) :
    Divisor.degree D = Finsupp.degree D := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.degree_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have h1 : P.deg = 1 := (AlgebraicCurve.Place.isRational_iff_deg_eq_one P).mp (h P hP)
  simp [h1]

theorem degree_filter (D : Divisor K F) (p : Place K F → Prop) [DecidablePred p] :
    Finsupp.degree (D.filter p) = ∑ P ∈ D.support.filter p, D P := by
  rw [Finsupp.degree_apply, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hP).2]

theorem sum_eq_degree (D : Divisor K F) : (D.sum fun _ n => n) = Finsupp.degree D := by
  rw [Finsupp.degree_apply, Finsupp.sum]

theorem mapDomain_apply_nonneg {α β : Type*} (φ : α → β) (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a) (b : β) :
    0 ≤ Finsupp.mapDomain φ D b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a _ => ?_
  show 0 ≤ (Finsupp.single (φ a) (D a)) b
  rw [Finsupp.single_apply]
  split_ifs
  · exact hD a
  · exact le_rfl

theorem eq_zero_of_nonneg_of_degree_eq_zero {α : Type*} (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a)
    (hdeg : Finsupp.degree D = 0) : D = 0 := by
  classical
  rw [Finsupp.degree_apply] at hdeg
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hD a)).mp hdeg
  ext a
  by_cases ha : a ∈ D.support
  · exact h a ha
  · exact Finsupp.notMem_support_iff.mp ha

end PlaceFacts

section Infinite

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem infinite_place : Infinite (Place K F) := by
  obtain ⟨t, ht, hfin, -⟩ := (IsCurveOver.exists_separating_transcendental (K := K) (F := F))
  haveI := hfin

  have hpole : ∀ {f : F}, Transcendental K f → ∃ v : Place K F, v.ord f < 0 := by
    intro f hf
    haveI := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental t hf
    classical
    have hf0 : f ≠ 0 := by rintro rfl; exact hf isAlgebraic_zero
    obtain ⟨Df, hDf, -⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor f hf0
    let D : Divisor K F := Finsupp.onFinset Df.support (fun v => max 0 (-v.ord f)) (by
        intro v hv
        rw [Finsupp.mem_support_iff, hDf v]
        intro h0; apply hv; simp [h0])
    have hD : ∀ v, D v = max 0 (-v.ord f) := fun v => by simp [D, Finsupp.onFinset_apply]
    have hdeg := AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental f hf D hD
    have hpos : 0 < Module.finrank (IntermediateField.adjoin K ({f} : Set F)) F := Module.finrank_pos
    have hne : D ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hdeg
      omega
    obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hne
    refine ⟨v, ?_⟩
    rw [hD v] at hv
    simp only [Finsupp.coe_zero, Pi.zero_apply, ne_eq] at hv
    by_contra hge
    apply hv
    rw [max_eq_left]
    omega
  have hz : ∀ a : K, ∃ v : Place K F, 0 < v.ord (t - algebraMap K F a) := by
    intro a
    have hta : Transcendental K (t - algebraMap K F a)⁻¹ := by
      intro halg
      apply ht
      have h1 : IsAlgebraic K (t - algebraMap K F a) := by simpa using halg.inv
      simpa using h1.add (isAlgebraic_algebraMap a)
    obtain ⟨v, hv⟩ := hpole hta
    refine ⟨v, ?_⟩
    rw [Place.ord_inv] at hv
    omega
  choose z hz using hz
  refine Infinite.of_injective z ?_
  intro a b hab
  by_contra hne
  have ha := hz a
  have hb := hz b
  rw [← hab] at hb
  have hta0 : t - algebraMap K F a ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have htb0 : t - algebraMap K F b ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hb; exact lt_irrefl _ hb
  have hlt : ∀ {f : F}, f ≠ 0 → 0 < (z a).ord f → (z a).adicValuation f < 1 := by
    intro f hf0 h
    rw [(z a).adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have h1 := hlt hta0 ha
  have h2 := hlt htb0 hb
  have hab0 : (b - a : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h3 : (z a).adicValuation (algebraMap K F (b - a)) = 1 := by
    rw [(z a).adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hab0), Place.ord_algebraMap, neg_zero,
      WithZero.exp_zero]
  have hid : algebraMap K F (b - a) = (t - algebraMap K F a) - (t - algebraMap K F b) := by
    rw [map_sub]; ring
  rw [hid] at h3
  have h4 := Valuation.map_sub (z a).adicValuation (t - algebraMap K F a) (t - algebraMap K F b)
  rw [h3] at h4
  rcases le_max_iff.mp h4 with h | h
  · exact absurd h1 (not_lt.mpr h)
  · exact absurd h2 (not_lt.mpr h)

omit [Algebra.EssFiniteType K F] in

theorem degree_eq_finsuppDegree' (D : Divisor K F) : Divisor.degree D = Finsupp.degree D :=
  degree_eq_finsuppDegree D fun P _ =>
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one P).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed P)

end Infinite

section DivisorFacts

theorem mapDomain_apply_eq_zero_of_forall_ne {α β : Type*} (φ : α → β) (D : α →₀ ℤ) (b : β)
    (h : ∀ a ∈ D.support, φ a ≠ b) : Finsupp.mapDomain φ D b = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    show (Finsupp.single (φ a) (D a)) b = 0
    rw [Finsupp.single_apply, if_neg (h a ha)]

end DivisorFacts

section ChartFacts

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_ne_zero_imp_ne_zero (C : ComponentChart A F Fbar) {c : L} {f : F}
    (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hc0
  have h0 : (⟨(0 : L) • f, hc⟩ : C.integers) = 0 := Subtype.ext (zero_smul L f)
  rw [h0, map_zero]

@[reducible] def toRP (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem ne_zero_of_residue_ne_zero (C : ComponentChart A F Fbar) {u : F} (hu : u ∈ C.integers)
    (h : C.residue ⟨u, hu⟩ ≠ 0) : u ≠ 0 := by
  rintro rfl
  apply h
  have h0 : (⟨(0 : F), hu⟩ : C.integers) = 0 := rfl
  rw [h0, map_zero]

theorem isAttached_transport (An' : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hatt : An'.IsAttached C x) {y : F} (hy : An'.param = y) {S : Set (Place L F)}
    (hS : An'.dom = S) :
    ∃ hz : y ∈ C.integers, x.ord (C.residue ⟨y, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) →
        ∀ P ∈ S, ∃ h : P.evalAt f * (P.evalAt y) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  subst hy; subst hS
  exact hatt.2

end ChartFacts

section TwoRadii

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem exists_fourth_root [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : (π : L) ≠ 0) :
    ∃ s : A, s ∈ maximalIdeal A ∧ (s : L) ≠ 0 ∧ s ^ 4 = π := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (π : L) (by norm_num : 0 < 4)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hπ0
    rw [← ht]; simp
  have htA : t ∈ A := by
    rcases A.mem_or_inv_mem t with h | h
    · exact h
    · exfalso
      have hinv : (π : L)⁻¹ ∈ A := by
        rw [← ht, ← inv_pow]
        exact pow_mem h 4
      have hunit : IsUnit π := by
        refine ⟨⟨π, ⟨(π : L)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
        · exact Subtype.ext (mul_inv_cancel₀ hπ0)
        · exact Subtype.ext (inv_mul_cancel₀ hπ0)
      exact (IsLocalRing.mem_maximalIdeal _).mp hπ hunit
  refine ⟨⟨t, htA⟩, ?_, ht0, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hπ
    have : π = (⟨t, htA⟩ : A) ^ 4 := Subtype.ext (by push_cast; exact ht.symm)
    rw [this]
    exact hu.pow 4
  · exact Subtype.ext (by push_cast; exact ht)

theorem exists_two_radii [IsAlgClosed L] (An : Annulus A F) (hmod0 : ((An.modulus : A) : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  obtain ⟨s, hs, hs0, hs4⟩ := exists_fourth_root An.modulus An.modulus_mem hmod0
  have hadm : ∀ (j : ℕ), 0 < j → j < 4 →
      ∃! P : Place L F, P ∈ An.dom ∧ P.evalAt An.param = ((s ^ j : A) : L) := by
    intro j hj hj4
    apply An.existsUnique_evalAt_eq
    · exact Ideal.pow_mem_of_mem _ hs j hj
    · push_cast; exact pow_ne_zero _ hs0
    · refine ⟨s ^ (4 - j), Ideal.pow_mem_of_mem _ hs _ (by omega), ?_⟩
      rw [← hs4]
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' hj4.le]
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := hadm 1 one_pos (by norm_num)
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := hadm 2 (by norm_num) (by norm_num)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁v, hQ₂v]
  push_cast
  rw [pow_one, Valuation.map_pow]
  intro heq
  have hvs0 : A.valuation (s : L) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hs0
  have hone : A.valuation (s : L) = 1 := by
    have : A.valuation (s : L) * 1 = A.valuation (s : L) * A.valuation (s : L) := by
      rw [mul_one, ← sq]; exact heq
    exact (mul_left_cancel₀ hvs0 this).symm
  rw [← ValuationSubring.valuation_eq_one_iff] at hone
  exact (IsLocalRing.mem_maximalIdeal _).mp hs hone

theorem exists_sqrt [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : (π : L) ≠ 0) :
    ∃ s : A, s ∈ maximalIdeal A ∧ (s : L) ≠ 0 ∧ s ^ 2 = π := by
  obtain ⟨t, ht, ht0, ht4⟩ := exists_fourth_root π hπ hπ0
  refine ⟨t ^ 2, Ideal.pow_mem_of_mem _ ht 2 (by norm_num), by push_cast; exact pow_ne_zero _ ht0, ?_⟩
  rw [← pow_mul]; exact ht4

end TwoRadii

section Mass

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fs : Type*} [Field Fs] [Algebra (ResidueField A) Fs]
variable {Ft : Type*} [Field Ft] [Algebra (ResidueField A) Ft]

theorem annulus_mass_one [IsAlgClosed L]
    (An An' : Annulus A F) (Cs : ComponentChart A F Fs) (Ct : ComponentChart A F Ft)
    (xs : Place (ResidueField A) Fs) (xt : Place (ResidueField A) Ft)
    (hdom : An'.dom = An.dom) (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hzz : An'.param * An.param = algebraMap L F (An.modulus : L))
    (hs : An.IsAttached Cs xs) (ht : An'.IsAttached Ct xt)
    (h : F) (hhs : h ∈ Cs.integers) (hhs0 : Cs.residue ⟨h, hhs⟩ ≠ 0)
    (hht : h ∈ Ct.integers) (hht0 : Ct.residue ⟨h, hht⟩ ≠ 0)
    (E : Divisor L F) (hEsupp : ∀ P ∈ E.support, P ∈ An.dom) (hE : ∀ P ∈ An.dom, E P = P.ord h) :
    (E.sum fun _ n => n) = xs.ord (Cs.residue ⟨h, hhs⟩) + xt.ord (Ct.residue ⟨h, hht⟩) := by
  classical
  have hz0 : An.param ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hzz
    exact hmod0 ((map_eq_zero _).mp hzz.symm)
  have hkey : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ := by
    rw [← hzz, mul_inv_cancel_right₀ hz0]
  obtain ⟨hza, hxa1, hslope_a⟩ := hs.2
  obtain ⟨hzb, hxb1, hslope_b⟩ := isAttached_transport An' Ct xt ht hkey hdom
  have hwide := exists_two_radii An hmod0
  have hh0 : h ≠ 0 := ne_zero_of_residue_ne_zero Cs hhs hhs0
  have heq : (algebraMap L F (1 : L))⁻¹ * h = h := by rw [map_one, inv_one, one_mul]
  have hhb : (algebraMap L F (1 : L))⁻¹ * h ∈ Ct.integers := by rw [heq]; exact hht
  have hsub : (⟨(algebraMap L F (1 : L))⁻¹ * h, hhb⟩ : Ct.integers) = ⟨h, hht⟩ := Subtype.ext heq
  have hresb : Ct.residue ⟨(algebraMap L F (1 : L))⁻¹ * h, hhb⟩ ≠ 0 := by rw [hsub]; exact hht0
  obtain ⟨hmass, -⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (toRP Cs) xs hza hxa1 hslope_a (toRP Ct) xt hzb hxb1 hslope_b hwide
      h hh0 hhs hhs0 1 one_ne_zero hhb hresb E hEsupp hE
  rw [hmass]
  show xs.ord (Cs.residue ⟨h, hhs⟩) + xt.ord (Ct.residue ⟨_, hhb⟩) = _
  rw [hsub]

end Mass

end InjSol

set_option maxHeartbeats 6400000 in
open InjSol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
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
    (E : Fin n → Divisor L F) (hE : ∀ i, ∀ P ∈ (E i).support, P ∈ (C i).dom)
    (g : ∀ i, Fbar i) (hg0 : ∀ i, g i ≠ 0)
    (hg : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i),
      Finsupp.mapDomain (C i).placeMap (E i) Q = Q.ord (g i))
    (hglue : ∀ e, (xs e).evalAt (g (src e)) = (xt e).evalAt (g (tgt e)))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (hkE : (k : ℤ) • (∑ i, E i) ∈ Divisor.principal (K := L) (F := F)) :
    (∑ i, E i) ∈ Divisor.principal (K := L) (F := F) := by
  classical
  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hπL : ((π : A) : L) ≠ 0 := fun h => hπ0 (ZeroMemClass.coe_eq_zero.mp h)

  have huniq : ∀ {P : Place L F} {i i' : Fin n}, P ∈ (C i).dom → P ∈ (C i').dom → i = i' := by
    intro P i i' h1 h2
    rcases hcover P with ⟨l, -, hl, -⟩ | ⟨e, -, -, hno'⟩
    · exact (hl i h1).trans (hl i' h2).symm
    · exact absurd h1 (hno' i)
  have hnode_g : ∀ i, ∀ x ∈ (C i).nodes, x.ord (g i) = 0 := by
    intro i x hx
    rw [← hg i x]
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun P hP h => ?_
    exact (C i).placeMap_not_mem_nodes P (hE i P hP) (h ▸ hx)
  have hEnode : ∀ i (D : Divisor L F), (∀ P ∈ D.support, P ∈ (C i).dom) →
      ∀ x ∈ (C i).nodes, Finsupp.mapDomain (C i).placeMap D x = 0 := by
    intro i D hD x hx
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun P hP h => ?_
    exact (C i).placeMap_not_mem_nodes P (hD P hP) (h ▸ hx)

  have hsumE_dom : ∀ {i P}, P ∈ (C i).dom → (∑ l, E l) P = E i P := by
    intro i P hP
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · intro l _ hli
      by_contra h
      exact hli (huniq (hE l P (Finsupp.mem_support_iff.mpr h)) hP)
    · intro h; exact absurd (Finset.mem_univ i) h
  have hsumE_ann : ∀ {e P}, P ∈ (An e).dom → (∑ l, E l) P = 0 := by
    intro e P hP
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_contra h
    rcases hcover P with ⟨i', -, -, hno⟩ | ⟨e', -, -, hno⟩
    · exact hno e hP
    · exact hno l (hE l P (Finsupp.mem_support_iff.mpr h))

  have finish : ∀ (G : F) (hGi : ∀ i, G ∈ (C i).integers), (∀ i, (C i).residue ⟨G, hGi i⟩ = g i) →
      ∀ (DG : Divisor L F), (∀ P, DG P = P.ord G) →
      ∀ i, Finsupp.mapDomain (C i).placeMap (E i - DG.filter (fun P => P ∈ (C i).dom)) = 0 := by
    intro G hGi hres DG hDG i
    have hres0 : (C i).residue ⟨G, hGi i⟩ ≠ 0 := by rw [hres i]; exact hg0 i
    have hsupp : ∀ P ∈ (DG.filter (fun P => P ∈ (C i).dom)).support, P ∈ (C i).dom := by
      intro P hP
      rw [Finsupp.support_filter, Finset.mem_filter] at hP
      exact hP.2
    have hms : Finsupp.mapDomain (C i).placeMap (E i - DG.filter (fun P => P ∈ (C i).dom)) =
        Finsupp.mapDomain (C i).placeMap (E i) -
          Finsupp.mapDomain (C i).placeMap (DG.filter (fun P => P ∈ (C i).dom)) :=
      map_sub (Finsupp.mapDomain.addMonoidHom _) _ _
    rw [hms]
    ext Q
    rw [Finsupp.sub_apply, Finsupp.zero_apply, sub_eq_zero]
    by_cases hQ : Q ∈ (C i).nodes
    · rw [hEnode i (E i) (hE i) Q hQ, hEnode i _ hsupp Q hQ]
    · rw [hg i Q, ← hres i]
      exact ((C i).mapDomain_placeMap ⟨G, hGi i⟩ hres0 (DG.filter fun P => P ∈ (C i).dom)
        (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hDG P])
        (fun P hP => Finsupp.filter_apply_neg _ _ hP) Q hQ).symm
  rcases Nat.eq_zero_or_pos m with hm | hm
  ·
    have hconn :=
      AlgebraicCurve.SemistableCovering.exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [show (∑ i : Fin 0, E i) = 0 from Finset.sum_of_isEmpty _]
      exact zero_mem _
    obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hn1 : ∀ i : Fin n, i = i₀ := by
      intro i
      by_contra hne
      obtain ⟨e, -⟩ := hconn {i₀} ⟨i₀, Finset.mem_singleton_self _⟩
        ⟨i, Finset.mem_compl.mpr (by rwa [Finset.mem_singleton])⟩
      exact absurd e.isLt (by omega)

    obtain ⟨Gint, hGint⟩ := (C i₀).residue_surjective (g i₀)
    set G : F := (Gint : F) with hGdef
    have hGi : ∀ i, G ∈ (C i).integers := fun i => by rw [hn1 i]; exact Gint.2
    have hresG : ∀ i, (C i).residue ⟨G, hGi i⟩ = g i := by
      intro i
      obtain rfl := hn1 i
      rw [← hGint]
    have hG0 : G ≠ 0 := ne_zero_of_residue_ne_zero (C i₀) (hGi i₀) (by rw [hresG]; exact hg0 i₀)
    obtain ⟨DG, hDG, -⟩ := (IsCurveOver.hasPrincipalDivisors (K := L) (F := F)).exists_divisor G hG0
    have hzero := finish G hGi hresG DG hDG

    have hall : ∀ P : Place L F, ∃ i, P ∈ (C i).dom := by
      intro P
      rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, -, -, -⟩
      · exact ⟨i, hi⟩
      · exact absurd e.isLt (by omega)
    have hDGsum : DG = ∑ i, DG.filter (fun P => P ∈ (C i).dom) := by
      ext P
      obtain ⟨i, hi⟩ := hall P
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · rw [Finsupp.filter_apply_pos _ _ hi]
      · intro l _ hli
        exact Finsupp.filter_apply_neg _ _ fun h => hli (huniq h hi)
      · intro h; exact absurd (Finset.mem_univ i) h
    have key :=
      AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
        A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc (by simpa using hgenus) Mdl Dsc
        k hk (fun i => E i - DG.filter (fun P => P ∈ (C i).dom)) (fun i P hP => ?_) hzero
        (ι := Fin 0) Fin.elim0 Fin.elim0 Fin.elim0 (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0) ?_
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at key
      rw [Finset.sum_sub_distrib, ← hDGsum] at key
      have := add_mem key (Divisor.mem_principal.mpr ⟨G, hG0, hDG⟩)
      rwa [sub_add_cancel] at this
    · have h := Finsupp.mem_support_iff.mp hP
      rw [Finsupp.sub_apply] at h
      by_cases h1 : E i P = 0
      · rw [h1, zero_sub, neg_ne_zero] at h
        by_contra hdom
        exact h (Finsupp.filter_apply_neg _ _ hdom)
      · exact hE i P (Finsupp.mem_support_iff.mpr h1)
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      rw [Finset.sum_sub_distrib, ← hDGsum, smul_sub]
      exact sub_mem hkE (AddSubgroup.zsmul_mem _ (Divisor.mem_principal.mpr ⟨G, hG0, hDG⟩) _)

  set e₀ : Fin m := ⟨0, hm⟩ with he₀

  obtain ⟨ϖ, hϖm, hϖ0, hϖ2⟩ := exists_sqrt π hπ hπL
  have hϖne : ϖ ≠ 0 := fun h => hϖ0 (by rw [h]; rfl)
  have hw' : ∀ e, ∃ u : Aˣ, (An e).modulus = u * ϖ ^ (2 * w e) := by
    intro e
    obtain ⟨u, hu⟩ := hw e
    exact ⟨u, by rw [hu, pow_mul, hϖ2]⟩
  have hwpos : ∀ e, 0 < w e := by
    intro e
    obtain ⟨u, hu⟩ := hw e
    refine Nat.pos_of_ne_zero ?_
    rintro h0
    rw [h0, pow_zero, mul_one] at hu
    have hmax := (An e).modulus_mem
    rw [hu, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
    exact hmax u.isUnit

  set d : ℕ := w e₀ with hd
  have hu'unit : IsUnit (1 + π : A) := by
    by_contra hnu
    have hmem : (1 + π : A) ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : (1 : A) ∈ maximalIdeal A := by
      have := Ideal.sub_mem _ hmem hπ
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one
  set u' : Aˣ := hu'unit.unit with hu'
  have hu'val : (u' : A) = 1 + π := hu'unit.unit_spec
  have hϖd_mem : ϖ ^ d ∈ maximalIdeal A := Ideal.pow_mem_of_mem _ hϖm d (hwpos e₀)
  have hϖdL : ((ϖ ^ d : A) : L) ≠ 0 := by push_cast; exact pow_ne_zero _ hϖ0
  obtain ⟨u₀, hu₀⟩ := hw' e₀
  have hadm : ∀ v : Aˣ, ∃ m' ∈ maximalIdeal A, ((An e₀).modulus : L) = (((v : A) * ϖ ^ d : A) : L) * m' := by
    intro v
    refine ⟨(v⁻¹ : Aˣ) * u₀ * ϖ ^ d, Ideal.mul_mem_left _ _ hϖd_mem, ?_⟩
    rw [hu₀]
    push_cast
    have : ((ϖ : A) : L) ^ (2 * w e₀) = ((ϖ : A) : L) ^ d * ((ϖ : A) : L) ^ d := by
      rw [← pow_add, hd, two_mul]
    rw [this]
    have hvv : ((v : A) : L) * (((v⁻¹ : Aˣ) : A) : L) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    linear_combination (-(((u₀ : A) : L) * ((ϖ : A) : L) ^ d * ((ϖ : A) : L) ^ d)) * hvv
  obtain ⟨P, ⟨hP, hPz⟩, -⟩ := (An e₀).existsUnique_evalAt_eq ((1 : Aˣ) * ϖ ^ d)
    (Ideal.mul_mem_left _ _ hϖd_mem) (by push_cast; rw [one_mul]; exact hϖdL) (hadm 1)
  obtain ⟨P', ⟨hP', hP'z⟩, -⟩ := (An e₀).existsUnique_evalAt_eq ((u' : A) * ϖ ^ d)
    (Ideal.mul_mem_left _ _ hϖd_mem)
    (by push_cast; exact mul_ne_zero (by rw [hu'val]; push_cast; exact_mod_cast hu'unit.ne_zero) hϖdL)
    (hadm u')
  have hPP' : P ≠ P' := by
    intro h
    rw [h, hP'z] at hPz
    have h1 : ((u' : A) : L) * ((ϖ ^ d : A) : L) = 1 * ((ϖ ^ d : A) : L) := by
      have := hPz; push_cast at this ⊢; linear_combination this
    have h2 := mul_right_cancel₀ hϖdL h1
    rw [hu'val] at h2
    push_cast at h2
    exact hπL (by linear_combination h2)
  have hPA : P.evalAt (An e₀).param ∈ A := by rw [hPz]; exact SetLike.coe_mem _
  have hP'A : P'.evalAt (An e₀).param ∈ A := by rw [hP'z]; exact SetLike.coe_mem _
  have hPd : (⟨P.evalAt (An e₀).param, hPA⟩ : A) = (1 : Aˣ) * ϖ ^ d := Subtype.ext hPz
  have hP'd : (⟨P'.evalAt (An e₀).param, hP'A⟩ : A) = u' * ϖ ^ d := Subtype.ext hP'z
  have htwist : IsLocalRing.residue A (((1 : Aˣ) : A) * ↑(u'⁻¹)) = 1 := by
    have h1 : IsLocalRing.residue A (u' : A) = 1 := by
      rw [hu'val, map_add, map_one, (IsLocalRing.residue_eq_zero_iff _).mpr hπ, add_zero]
    have h2 : IsLocalRing.residue A (u' : A) * IsLocalRing.residue A ((u'⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [h1, one_mul] at h2
    rw [Units.val_one, one_mul, h2]

  have hdomne : ∀ i, ∃ Pi : Place L F, Pi ∈ (C i).dom := by
    intro i
    haveI := infinite_place (K := ResidueField A) (F := Fbar i)
    obtain ⟨Q, hQ⟩ := Infinite.exists_notMem_finset (C i).nodes
    obtain ⟨T, hT, -, -, -, huq⟩ := hdisc i Q hQ
    obtain ⟨Pi, ⟨hPi, -, -⟩, -⟩ := huq 0 (Ideal.zero_mem _)
    exact ⟨Pi, hPi⟩
  choose Pc hPc using hdomne
  let Eneg : Fin n → Divisor L F := fun i => Finsupp.mapRange (fun z : ℤ => max 0 (-z)) (by simp) (E i)
  have hEneg_apply : ∀ i P, Eneg i P = max 0 (-(E i P)) := fun i P => Finsupp.mapRange_apply
  have hEneg_supp : ∀ i, ∀ P ∈ (Eneg i).support, P ∈ (C i).dom := fun i P hP =>
    hE i P (Finsupp.support_mapRange hP)
  let N : Fin n → ℕ := fun i =>
    (2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ)).toNat
  let E' : Fin n → Divisor L F := fun i => Eneg i + (N i : ℤ) • Finsupp.single (Pc i) 1
  have hE'apply : ∀ i P, E' i P = max 0 (-(E i P)) + (N i : ℤ) * (Finsupp.single (Pc i) (1 : ℤ)) P := by
    intro i P
    simp only [E', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hEneg_apply]
  have hE'nonneg : ∀ i P, 0 ≤ E' i P := by
    intro i P
    rw [hE'apply]
    have h1 : 0 ≤ max 0 (-(E i P)) := le_max_left _ _
    have h2 : 0 ≤ (N i : ℤ) * (Finsupp.single (Pc i) (1 : ℤ)) P :=
      mul_nonneg (Int.natCast_nonneg _) (by rw [Finsupp.single_apply]; split_ifs <;> norm_num)
    linarith
  have hE'supp : ∀ i, ∀ P ∈ (E' i).support, P ∈ (C i).dom := by
    intro i P hP
    have h := Finsupp.mem_support_iff.mp hP
    rw [hE'apply, Finsupp.single_apply] at h
    by_cases hPc' : Pc i = P
    · rw [← hPc']; exact hPc i
    · rw [if_neg hPc', mul_zero, add_zero] at h
      exact hEneg_supp i P (Finsupp.mem_support_iff.mpr (by rw [hEneg_apply]; exact h))
  have hdegBar : ∀ i (D : Divisor L F), (∀ P ∈ D.support, P ∈ (C i).dom) →
      Divisor.degree (Finsupp.mapDomain (C i).placeMap D) = Finsupp.degree D := by
    intro i D hD
    rw [degree_eq_finsuppDegree _ (fun Q _ => hratBar i Q), Finsupp.degree_mapDomain]
  have hdegE' : ∀ i, 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (E' i)) := by
    intro i
    rw [hdegBar i (E' i) (hE'supp i)]
    have h1 : Finsupp.degree (E' i) = Finsupp.degree (Eneg i) + N i := by
      simp only [E', map_add, map_zsmul, Finsupp.degree_single, smul_eq_mul, mul_one]
    have h2 : 0 ≤ Finsupp.degree (Eneg i) := by
      rw [Finsupp.degree_apply]
      exact Finset.sum_nonneg fun P _ => by rw [hEneg_apply]; exact le_max_left _ _
    rw [h1]
    have h3 : 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤ (N i : ℤ) :=
      Int.self_le_toNat _
    linarith

  have hsRR : ∀ i, g i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (E' i)) := by
    intro i
    rw [mem_riemannRochSpace_iff]
    intro Q
    right
    rw [← hg i Q]
    have hsum : 0 ≤ Finsupp.mapDomain (C i).placeMap (E' i + E i) Q :=
      mapDomain_apply_nonneg _ _ (fun P => by
        rw [Finsupp.add_apply, hE'apply, Finsupp.single_apply]
        have h1 := le_max_right 0 (-(E i P))
        have h2 := Int.natCast_nonneg (N i)
        split_ifs
        · nlinarith
        · nlinarith) Q
    rw [Finsupp.mapDomain_add, Finsupp.add_apply] at hsum
    linarith
  have hsnode : ∀ i, ∀ x ∈ (C i).nodes, g i ∈ x.toValuationSubring ∧ x.ord (g i) = 0 := fun i x hx =>
    ⟨(AlgebraicCurve.Place.mem_iff_ord_nonneg x (hg0 i)).mpr (hnode_g i x hx).ge, hnode_g i x hx⟩

  obtain ⟨G, hG0, hGRR, hGres⟩ :=
    AlgebraicCurve.SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne
      A ϖ hϖm hϖne hrk F n m Fbar hratBar C hratF An An' src tgt xs xt (fun e => 2 * w e) hpair hw' hatt hnodes
      hcover hdisc hgenus E' hE'supp (fun i => Finsupp.le_def.mpr fun P => by
        rw [Finsupp.coe_zero, Pi.zero_apply]; exact hE'nonneg i P) hdegE'
      e₀ P P' hP hP' hPP' d 1 u' hPA hP'A hPd hP'd g hsRR hsnode (fun e _ => hglue e)
      (by rw [htwist, one_mul]; exact hglue e₀)
  choose hGi hGres using hGres
  have hGres0 : ∀ i, (C i).residue ⟨G, hGi i⟩ ≠ 0 := fun i => by rw [hGres i]; exact hg0 i
  obtain ⟨DG, hDG, hdegDG⟩ := (IsCurveOver.hasPrincipalDivisors (K := L) (F := F)).exists_divisor G hG0
  have hzero := finish G hGi hGres DG hDG

  have hGord : ∀ Q : Place L F,
      -(((∑ i, E' i) + Finsupp.single P (1 : ℤ) - Finsupp.single P' (1 : ℤ) : Divisor L F) Q) ≤ Q.ord G := by
    intro Q
    rcases (mem_riemannRochSpace_iff.mp hGRR) Q with h | h
    · exact absurd h hG0
    · exact h
  have hsumE'_ann : ∀ {e Q}, Q ∈ (An e).dom → (∑ l, E' l) Q = 0 := by
    intro e Q hQ
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_contra h
    rcases hcover Q with ⟨i', -, -, hno⟩ | ⟨e', -, -, hno⟩
    · exact hno e hQ
    · exact hno l (hE'supp l Q (Finsupp.mem_support_iff.mpr h))
  have hann_uniq : ∀ {e e' : Fin m} {Q : Place L F}, Q ∈ (An e).dom → Q ∈ (An e').dom → e = e' := by
    intro e e' Q h1 h2
    rcases hcover Q with ⟨i', -, -, hno⟩ | ⟨e'', -, hu, -⟩
    · exact absurd h1 (hno e)
    · exact (hu e h1).trans (hu e' h2).symm

  have hmass : ∀ e, Finsupp.degree (DG.filter fun Q => Q ∈ (An e).dom) = 0 := by
    intro e
    rw [← sum_eq_degree]
    have h := annulus_mass_one (An e) (An' e) (C (src e)) (C (tgt e)) (xs e) (xt e) (hpair e).1
      (hpair e).2.2.1 (hpair e).2.2.2 (hatt e).1 (hatt e).2 G (hGi _) (hGres0 _) (hGi _) (hGres0 _)
      (DG.filter fun Q => Q ∈ (An e).dom)
      (fun Q hQ => by
        rw [Finsupp.support_filter, Finset.mem_filter] at hQ
        exact hQ.2)
      (fun Q hQ => by rw [Finsupp.filter_apply_pos _ _ hQ, hDG Q])
    rw [h, hGres, hGres, hnode_g _ _ (hatt e).1.1, hnode_g _ _ (hatt e).2.1, add_zero]

  have hoff : ∀ e, e ≠ e₀ → ∀ Q ∈ (An e).dom, DG Q = 0 := by
    intro e he
    have hnn : ∀ Q, 0 ≤ (DG.filter fun Q => Q ∈ (An e).dom) Q := by
      intro Q
      by_cases hQ : Q ∈ (An e).dom
      · rw [Finsupp.filter_apply_pos _ _ hQ, hDG Q]
        have h := hGord Q
        have hQP : Q ≠ P := fun h' => he (hann_uniq hQ (h' ▸ hP))
        have hQP' : Q ≠ P' := fun h' => he (hann_uniq hQ (h' ▸ hP'))
        rw [Finsupp.sub_apply, Finsupp.add_apply, hsumE'_ann hQ, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (Ne.symm hQP), if_neg (Ne.symm hQP')] at h
        simpa using h
      · rw [Finsupp.filter_apply_neg _ _ hQ]
    have h0 := eq_zero_of_nonneg_of_degree_eq_zero _ hnn (hmass e)
    intro Q hQ
    have := DFunLike.congr_fun h0 Q
    rwa [Finsupp.filter_apply_pos _ _ hQ] at this

  have hon : (DG.filter fun Q => Q ∈ (An e₀).dom) = Finsupp.single P' 1 - Finsupp.single P 1 := by
    set X : Divisor L F := (DG.filter fun Q => Q ∈ (An e₀).dom) + Finsupp.single P 1 - Finsupp.single P' 1
      with hX
    have hnn : ∀ Q, 0 ≤ X Q := by
      intro Q
      rw [hX, Finsupp.sub_apply, Finsupp.add_apply]
      by_cases hQ : Q ∈ (An e₀).dom
      · rw [Finsupp.filter_apply_pos _ _ hQ, hDG Q]
        have h := hGord Q
        rw [Finsupp.sub_apply, Finsupp.add_apply, hsumE'_ann hQ, zero_add] at h
        linarith
      · have hQP : P ≠ Q := fun h' => hQ (h' ▸ hP)
        have hQP' : P' ≠ Q := fun h' => hQ (h' ▸ hP')
        rw [Finsupp.filter_apply_neg _ _ hQ, Finsupp.single_apply, Finsupp.single_apply, if_neg hQP,
          if_neg hQP']
        norm_num
    have hdegX : Finsupp.degree X = 0 := by
      rw [hX, map_sub, map_add, hmass e₀, Finsupp.degree_single, Finsupp.degree_single]; ring
    have h0 := eq_zero_of_nonneg_of_degree_eq_zero X hnn hdegX
    rw [hX] at h0

    calc (DG.filter fun Q => Q ∈ (An e₀).dom)
        = ((DG.filter fun Q => Q ∈ (An e₀).dom) + Finsupp.single P 1 - Finsupp.single P' 1)
            - Finsupp.single P 1 + Finsupp.single P' 1 := by abel
      _ = Finsupp.single P' 1 - Finsupp.single P 1 := by rw [h0]; abel

  have hDGsplit : DG = (∑ i, DG.filter fun Q => Q ∈ (C i).dom) + (Finsupp.single P' 1 - Finsupp.single P 1) := by
    rw [← hon]
    ext Q
    rw [Finsupp.add_apply, Finsupp.finsetSum_apply]
    rcases hcover Q with ⟨i, hi, hu, hno⟩ | ⟨e, he, hu, hno⟩
    · rw [Finset.sum_eq_single i, Finsupp.filter_apply_pos _ _ hi, Finsupp.filter_apply_neg _ _ (hno e₀),
        add_zero]
      · intro l _ hli
        exact Finsupp.filter_apply_neg _ _ fun h => hli (hu l h)
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [Finset.sum_eq_zero (fun l _ => Finsupp.filter_apply_neg _ _ (hno l)), zero_add]
      by_cases hee : e = e₀
      · subst hee
        rw [Finsupp.filter_apply_pos _ _ he]
      · rw [Finsupp.filter_apply_neg _ _ (fun h => hee (hann_uniq he h)), hoff e hee Q he]

  have hzP : P.evalAt (An e₀).param = ((ϖ ^ d : A) : L) := by rw [hPz]; push_cast; ring
  have hzP' : P'.evalAt (An e₀).param = (1 + ((π : A) : L)) * ((ϖ ^ d : A) : L) := by
    rw [hP'z]; push_cast; rw [hu'val]; push_cast; ring
  have h1π0 : (1 + ((π : A) : L)) ≠ 0 := by
    have := hu'unit.ne_zero
    intro h; apply this; apply Subtype.ext; push_cast; exact h
  have key :=
    AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc (by simpa using hgenus) Mdl Dsc
      k hk (fun i => E i - DG.filter (fun Q => Q ∈ (C i).dom)) (fun i Q hQ => ?_) hzero
      (ι := Fin 1) (fun _ => e₀) (fun _ => 1) (fun _ => ![P, P', P', P'])
      (fun j l => by fin_cases l <;> simp [hP, hP']) (fun j => ?_) (fun j => ?_) ?_
  ·
    have hsimp : (∑ j : Fin 1, (1 : ℤ) • (Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 0) (1 : ℤ) +
        Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 1) 1 -
        Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 2) 1 -
        Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 3) 1)) =
        Finsupp.single P 1 - Finsupp.single P' 1 := by
      rw [Fin.sum_univ_one, one_smul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      abel
    rw [hsimp, Finset.sum_sub_distrib] at key
    have hEq : (∑ i, E i) - (∑ i, DG.filter fun Q => Q ∈ (C i).dom) + (Finsupp.single P 1 - Finsupp.single P' 1)
        = (∑ i, E i) - DG := by
      conv_rhs => rw [hDGsplit]
      abel
    rw [hEq] at key
    have := add_mem key (Divisor.mem_principal.mpr ⟨G, hG0, hDG⟩)
    rwa [sub_add_cancel] at this
  ·
    have h := Finsupp.mem_support_iff.mp hQ
    rw [Finsupp.sub_apply] at h
    by_cases h1 : E i Q = 0
    · rw [h1, zero_sub, neg_ne_zero] at h
      by_contra hdom
      exact h (Finsupp.filter_apply_neg _ _ hdom)
    · exact hE i Q (Finsupp.mem_support_iff.mpr h1)
  ·
    refine ⟨u'⁻¹, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val]
    rw [hzP, hzP']
    have hinv : (((u'⁻¹ : Aˣ) : A) : L) * (1 + ((π : A) : L)) = 1 := by
      have h := congrArg (fun x : A => (x : L)) (u'.inv_mul : ((u'⁻¹ : Aˣ) : A) * (u' : A) = 1)
      push_cast at h
      rw [hu'val] at h
      push_cast at h
      exact h
    calc ((ϖ ^ d : A) : L) = ((((u'⁻¹ : Aˣ) : A) : L) * (1 + ((π : A) : L))) * ((ϖ ^ d : A) : L) := by
          rw [hinv, one_mul]
      _ = (((u'⁻¹ : Aˣ) : A) : L) * ((1 + ((π : A) : L)) * ((ϖ ^ d : A) : L)) := by ring
  ·
    refine ⟨-(π * ((u'⁻¹ : Aˣ) : A)), neg_mem (Ideal.mul_mem_right _ _ hπ), ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [hzP, hzP']
    have hinv : (((u'⁻¹ : Aˣ) : A) : L) * (1 + ((π : A) : L)) = 1 := by
      have h := congrArg (fun x : A => (x : L)) (u'.inv_mul : ((u'⁻¹ : Aˣ) : A) * (u' : A) = 1)
      push_cast at h
      rw [hu'val] at h
      push_cast at h
      exact h
    push_cast
    linear_combination (((ϖ : A) : L) ^ d * ((1 + ((π : A) : L)) * ((ϖ : A) : L) ^ d) * ((π : A) : L)) * hinv
  ·
    have hsimp : (∑ j : Fin 1, (1 : ℤ) • (Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 0) (1 : ℤ) +
        Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 1) 1 -
        Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 2) 1 -
        Finsupp.single ((![P, P', P', P'] : Fin 4 → Place L F) 3) 1)) =
        Finsupp.single P 1 - Finsupp.single P' 1 := by
      rw [Fin.sum_univ_one, one_smul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      abel
    rw [hsimp, Finset.sum_sub_distrib]
    have hEq : (∑ i, E i) - (∑ i, DG.filter fun Q => Q ∈ (C i).dom) + (Finsupp.single P 1 - Finsupp.single P' 1)
        = (∑ i, E i) - DG := by
      conv_rhs => rw [hDGsplit]
      abel
    rw [hEq, smul_sub]
    exact sub_mem hkE (AddSubgroup.zsmul_mem _ (Divisor.mem_principal.mpr ⟨G, hG0, hDG⟩) _)

end

end S_AlgebraicCurve_SemistableCovering_sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel (solution)
