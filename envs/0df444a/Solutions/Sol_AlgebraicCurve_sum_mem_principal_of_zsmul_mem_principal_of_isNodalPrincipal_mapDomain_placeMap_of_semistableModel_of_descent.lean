-- Prove2me | solution 1 for AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2f746607-42ea-51e8-9329-89fa4715e4ca

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_NodalPic0
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_forall_residue_eq_of_forall_evalAt_eq_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel
import Theorems.Thm_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
import Theorems.Thm_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
import Theorems.Thm_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
import Theorems.Thm_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
import Theorems.Thm_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap
import Theorems.Thm_AlgebraicGeometry_isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing

namespace RIPre

variable {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem mem_dom_of_mem_support (C : ComponentChart A F Fbar) (D : Divisor L F)
    (hD0 : ∀ P, P ∉ C.dom → D P = 0) : ∀ P ∈ D.support, P ∈ C.dom := by
  intro P hP
  by_contra h
  exact (Finsupp.mem_support_iff.mp hP) (hD0 P h)

theorem mapDomain_placeMap_apply_of_mem_nodes (C : ComponentChart A F Fbar) (D : Divisor L F)
    (hD : ∀ P ∈ D.support, P ∈ C.dom) {Q : Place (ResidueField A) Fbar} (hQ : Q ∈ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = 0 := by
  classical
  by_contra h
  have hQ' : Q ∈ (Finsupp.mapDomain C.placeMap D).support := Finsupp.mem_support_iff.mpr h
  obtain ⟨P, hP, hPQ⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hQ')
  exact C.placeMap_not_mem_nodes P (hD P hP) (hPQ ▸ hQ)

theorem mapDomain_placeMap_sub_filter_eq_zero (C : ComponentChart A F Fbar)
    (E : Divisor L F) (hE : ∀ P ∈ E.support, P ∈ C.dom)
    (gbar : Fbar) (hEg : ∀ v, Finsupp.mapDomain C.placeMap E v = v.ord gbar)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ = gbar) (hg0 : gbar ≠ 0)
    (Df : Divisor L F) (hDf : ∀ P, Df P = P.ord f) [DecidablePred fun P => P ∈ C.dom] :
    Finsupp.mapDomain C.placeMap (E - Df.filter fun P => P ∈ C.dom) = 0 := by
  classical
  have hres0 : C.residue ⟨f, hf⟩ ≠ 0 := by rw [hres]; exact hg0
  have hD : ∀ P ∈ C.dom, (Df.filter fun P => P ∈ C.dom) P = P.ord ((⟨f, hf⟩ : C.integers) : F) := by
    intro P hP; rw [Finsupp.filter_apply, if_pos hP, hDf P]
  have hD0 : ∀ P, P ∉ C.dom → (Df.filter fun P => P ∈ C.dom) P = 0 := by
    intro P hP; rw [Finsupp.filter_apply, if_neg hP]
  ext Q
  rw [Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hQ : Q ∈ C.nodes
  · rw [mapDomain_placeMap_apply_of_mem_nodes A C E hE hQ,
      mapDomain_placeMap_apply_of_mem_nodes A C _ (mem_dom_of_mem_support A C _ hD0) hQ, sub_zero]
  · rw [hEg Q, C.mapDomain_placeMap ⟨f, hf⟩ hres0 _ hD hD0 Q hQ, hres, sub_self]

theorem support_sub_filter_subset (C : ComponentChart A F Fbar) (E Df : Divisor L F)
    (hE : ∀ P ∈ E.support, P ∈ C.dom) [DecidablePred fun P => P ∈ C.dom] :
    ∀ P ∈ (E - Df.filter fun P => P ∈ C.dom).support, P ∈ C.dom := by
  intro P hP
  by_contra h
  apply Finsupp.mem_support_iff.mp hP
  rw [Finsupp.sub_apply, Finsupp.filter_apply, if_neg h, sub_zero]
  by_contra hne
  exact h (hE P (Finsupp.mem_support_iff.mpr hne))

end RIPre

namespace RIPre

theorem support_neg_filter_subset {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (S : Set (Place L F)) (Df : Divisor L F) [DecidablePred fun P => P ∈ S] :
    ∀ P ∈ (-(Df.filter fun P => P ∈ S)).support, P ∈ S := by
  intro P hP
  by_contra h
  apply Finsupp.mem_support_iff.mp hP
  rw [Finsupp.neg_apply, Finsupp.filter_apply, if_neg h, neg_zero]

theorem sum_sub_eq_sum_sub_filter_add_sum_neg_filter
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {n m : ℕ} {Fbar : Fin n → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (Df : Divisor L F)
    [∀ i, DecidablePred fun P => P ∈ (C i).dom] [∀ e, DecidablePred fun P => P ∈ (An e).dom] :
    ∀ P : Place L F, (∑ i, Di i) P - Df P =
      (∑ i, (Di i - Df.filter fun P => P ∈ (C i).dom) + ∑ e, -(Df.filter fun P => P ∈ (An e).dom)) P := by
  intro P
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.sub_apply, Finsupp.neg_apply, Finsupp.filter_apply,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rcases hcover P with ⟨i, hi, huniq, hnot⟩ | ⟨e, he, huniq, hnot⟩
  ·
    have h1 : ∑ j, (if P ∈ (C j).dom then Df P else 0) = Df P := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos hi]
      · intro j _ hji; rw [if_neg (fun hj => hji (huniq j hj))]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2 : ∑ e, (if P ∈ (An e).dom then Df P else 0) = 0 :=
      Finset.sum_eq_zero (fun e _ => by rw [if_neg (hnot e)])
    rw [h1, h2, neg_zero, add_zero]
  ·
    have h1 : ∑ j, (if P ∈ (C j).dom then Df P else 0) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [if_neg (hnot j)])
    have h2 : ∑ e', (if P ∈ (An e').dom then Df P else 0) = Df P := by
      rw [Finset.sum_eq_single e]
      · rw [if_pos he]
      · intro e' _ hne; rw [if_neg (fun h => hne (huniq e' h))]
      · intro h; exact absurd (Finset.mem_univ e) h
    have h3 : ∑ j, (Di j) P = 0 := Finset.sum_eq_zero (fun j _ => by
      by_contra hne; exact hnot j (hdom j P (Finsupp.mem_support_iff.mpr hne)))
    rw [h1, h2, h3, sub_zero]
    ring

end RIPre

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace ChartPrincipalMomentEngine

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  have := v.ord_coe_unit u
  simpa [u] using this

theorem ord_smul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap v hc, zero_add]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  have := v.evalAt_algebraMap_eq (0 : K)
  simpa using this

theorem degree_eq_sum_of_isRational (D : Divisor K F) (h : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp [Place.deg_eq_one_of_isRational (h v hv)]

end PlaceLemmas

section OneChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

@[reducible] def rp (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem const_ne_zero (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 :=
  (rp C).smul_const_ne_zero hc hres

theorem fun_ne_zero (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨c • (0 : F), hc⟩ : C.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem mapDomain_eq_ord_of_not_mem_nodes (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∉ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = Q.ord (C.residue ⟨c • f, hc⟩) := by
  refine C.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P hP => ?_) hDoff Q hQ
  rw [hDdom P hP]
  exact (ord_smul P (const_ne_zero C hc hres) (fun_ne_zero C hc hres)).symm

theorem mapDomain_eq_zero_of_mem_nodes (C : ComponentChart A F Fbar)
    (D : Divisor L F) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∈ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  show Finsupp.single (C.placeMap P) (D P) Q = 0
  rw [Finsupp.single_apply, if_neg]
  intro hPQ
  have hPdom : P ∈ C.dom := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (hDoff P h)
  exact C.placeMap_not_mem_nodes P hPdom (hPQ ▸ hQ)

theorem sum_mapDomain (C : ComponentChart A F Fbar) (D : Divisor L F) :
    ((Finsupp.mapDomain C.placeMap D).sum fun _ n => n) = D.sum fun _ n => n :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem sum_nodes_ord_eq_zero [HasPrincipalDivisors (ResidueField A) Fbar]
    (hrat : ∀ x : Place (ResidueField A) Fbar, x.IsRational)
    (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (hmass : (D.sum fun _ n => n) = 0) :
    ∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩) = 0 := by
  classical
  set g : Fbar := C.residue ⟨c • f, hc⟩ with hg
  obtain ⟨E, hE, hdegE⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) g hres

  set N : Divisor (ResidueField A) Fbar := ∑ x ∈ C.nodes, Finsupp.single x (x.ord g) with hN
  have hN_apply : ∀ y, N y = if y ∈ C.nodes then y.ord g else 0 := by
    intro y
    rw [hN, Finsupp.finsetSum_apply]
    split_ifs with hy
    · rw [Finset.sum_eq_single y (fun x _ hxy => by rw [Finsupp.single_apply, if_neg hxy])
        (fun h => (h hy).elim), Finsupp.single_eq_same]
    · exact Finset.sum_eq_zero fun x hx => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hy hx
  have hEeq : E = Finsupp.mapDomain C.placeMap D + N := by
    ext y
    rw [Finsupp.add_apply, hN_apply, hE y]
    by_cases hy : y ∈ C.nodes
    · rw [if_pos hy, mapDomain_eq_zero_of_mem_nodes C D hDoff y hy, zero_add]
    · rw [if_neg hy, mapDomain_eq_ord_of_not_mem_nodes C hc hres D hDdom hDoff y hy, add_zero]

  have hmassE : (E.sum fun _ n => n) = 0 := by
    rw [← degree_eq_sum_of_isRational E (fun v _ => hrat v)]
    exact hdegE
  have hmassN : (N.sum fun _ n => n) = ∑ x ∈ C.nodes, x.ord g := by
    rw [hN, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index rfl
  rw [hEeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_mapDomain, hmass, zero_add,
    hmassN] at hmassE
  exact hmassE

end OneChart

section OneAnnulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

private theorem transfer_end {I : ValuationSubring F} (res : I →+* Fb) (x : Place (ResidueField A) Fb)
    {S S' : Set (Place L F)} (hS : S = S') {p p' : F} (hp : p = p')
    (H : ∃ hz : p ∈ I, x.ord (res ⟨p, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) → ∀ P ∈ S,
        ∃ h : P.evalAt f * (P.evalAt p) ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) :
    ∃ hz : p' ∈ I, x.ord (res ⟨p', hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S', P.ord f = 0) → ∀ P ∈ S',
        ∃ h : P.evalAt f * (P.evalAt p') ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  subst hS; subst hp; exact H

theorem param_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) : An.param ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
  exact hne (by rw [h0, evalAt_zero])

theorem end_orders (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    {f : F} (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    (hN : ∀ P ∈ An.dom, N P = P.ord f) (hNsum : (N.sum fun _ k => k) = 0)
    (hNprod : (N.prod fun P k => A.valuation (P.evalAt An.param) ^ k) = 1)
    {ca : L} (hca : ca • f ∈ Ca.integers) (hresa : Ca.residue ⟨ca • f, hca⟩ ≠ 0)
    {cb : L} (hcb : cb • f ∈ Cb.integers) (hresb : Cb.residue ⟨cb • f, hcb⟩ ≠ 0) :
    xa.ord (Ca.residue ⟨ca • f, hca⟩) + xb.ord (Cb.residue ⟨cb • f, hcb⟩) = 0 ∧
    A.valuation ca * (A.valuation cb)⁻¹ *
        A.valuation (An.modulus : L) ^ (xb.ord (Cb.residue ⟨cb • f, hcb⟩)) = 1 := by
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₁
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hca0 : ca ≠ 0 := const_ne_zero Ca hca hresa
  have hcb0 : cb ≠ 0 := const_ne_zero Cb hcb hresb
  have hf0 : f ≠ 0 := fun_ne_zero Ca hca hresa

  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, Hb⟩ := hatt'
  obtain ⟨hzb, hxb, hslb⟩ := transfer_end Cb.residue xb hdom hp' Hb

  set c' : L := ca * cb⁻¹ with hc'
  have hc'0 : c' ≠ 0 := mul_ne_zero hca0 (inv_ne_zero hcb0)
  have hh0 : ca • f ≠ 0 := smul_ne_zero hca0 hf0
  have heq : (algebraMap L F c')⁻¹ * (ca • f) = cb • f := by
    have hca' : algebraMap L F ca ≠ 0 := (map_ne_zero _).mpr hca0
    rw [hc', Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀]
    field_simp
  have hhb : (algebraMap L F c')⁻¹ * (ca • f) ∈ Cb.integers := heq ▸ hcb
  have hsub : (⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ : Cb.integers) = ⟨cb • f, hcb⟩ :=
    Subtype.ext heq
  have hresb' : Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ ≠ 0 := by rw [hsub]; exact hresb

  have hordh : ∀ P ∈ An.dom, N P = P.ord (ca • f) := fun P hP => by
    rw [ord_smul P hca0 hf0]; exact hN P hP
  obtain ⟨hmass, hprod⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (rp Ca) xa hza hxa hsla (rp Cb) xb hzb hxb hslb ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩
      (ca • f) hh0 hca hresa c' hc'0 hhb hresb' N hNdom hordh
  rw [hNsum] at hmass
  rw [hNprod] at hprod

  have hordb : xb.ord ((rp Cb).residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) =
      xb.ord (Cb.residue ⟨cb • f, hcb⟩) := by
    show xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) = _
    rw [hsub]
  rw [hordb] at hmass hprod
  refine ⟨?_, ?_⟩
  · exact hmass.symm
  · rw [hc', map_mul, map_inv₀] at hprod
    exact hprod.symm

end OneAnnulus

section Wide

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem mem_of_pow_mem {r : L} {k : ℕ} (hk : 0 < k) (hr : r ^ k ∈ A) : r ∈ A := by
  rw [← A.valuation_le_one_iff] at hr ⊢
  rw [map_pow] at hr
  by_contra h
  have h' : 1 < A.valuation r := not_le.mp h
  have : 1 < A.valuation r ^ k := one_lt_pow₀ h' hk.ne'
  exact absurd hr (not_le.mpr this)

theorem mem_maximalIdeal_of_pow {r : A} {k : ℕ} {a : A} (ha : a ∈ maximalIdeal A) (hr : r ^ k = a) :
    r ∈ maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro hu
  exact ha (hr ▸ hu.pow k)

theorem wide_of_isAlgClosed [IsAlgClosed L] (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  set μ : A := An.modulus with hμ
  have hμm : μ ∈ maximalIdeal A := An.modulus_mem
  have hvμ1 : A.valuation (μ : L) < 1 := (A.valuation_lt_one_iff μ).mp hμm
  have hvμ0 : A.valuation (μ : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hmod0

  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 2) two_pos
  have hrA : r ∈ A := mem_of_pow_mem two_pos (hr ▸ μ.2)
  have hr' : (⟨r, hrA⟩ : A) ^ 2 = μ := Subtype.ext (by simpa using hr)
  have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hr'
  have hr0 : r ≠ 0 := by rintro rfl; apply hmod0; rw [← hr]; simp

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 3) three_pos
  have hsA : s ∈ A := mem_of_pow_mem three_pos (hs ▸ μ.2)
  have hs' : (⟨s, hsA⟩ : A) ^ 3 = μ := Subtype.ext (by simpa using hs)
  have hsm : (⟨s, hsA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hs'
  have hs0 : s ≠ 0 := by rintro rfl; apply hmod0; rw [← hs]; simp
  have htm : (⟨s, hsA⟩ : A) ^ 2 ∈ maximalIdeal A :=
    Ideal.pow_mem_of_mem _ hsm 2 two_pos

  obtain ⟨Q₁, ⟨hQ₁, hQ₁z⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0
    ⟨⟨r, hrA⟩, hrm, by rw [← hμ, ← hr]; simp [pow_two]⟩
  obtain ⟨Q₂, ⟨hQ₂, hQ₂z⟩, -⟩ := An.existsUnique_evalAt_eq (⟨s, hsA⟩ ^ 2) htm (by simpa using hs0)
    ⟨⟨s, hsA⟩, hsm, by rw [← hμ, ← hs]; simp [pow_succ]⟩
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁z, hQ₂z]
  intro hv

  have h1 : A.valuation r ^ 2 = A.valuation (μ : L) := by rw [← map_pow, hr]
  have h2 : A.valuation (((⟨s, hsA⟩ : A) ^ 2 : A) : L) ^ 3 = A.valuation (μ : L) ^ 2 := by
    rw [← map_pow, ← map_pow]
    congr 1
    push_cast
    rw [← hs]; ring
  have hv' : A.valuation r = A.valuation (((⟨s, hsA⟩ : A) ^ 2 : A) : L) := hv
  rw [← hv'] at h2

  have ha0 : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have : A.valuation (μ : L) = 1 := by
    have h3 : A.valuation r ^ 3 * 1 = A.valuation r ^ 3 * A.valuation r := by
      rw [mul_one, ← pow_succ, h2, ← h1, ← pow_mul]
    have h4 : A.valuation r = 1 := (mul_left_cancel₀ (pow_ne_zero 3 ha0) h3).symm
    rw [← h1, h4, one_pow]
  exact absurd this hvμ1.ne

end Wide

section Nodes

open Finset

variable {ι E : Type*} [Fintype E] [DecidableEq ι] {P : ι → Type*}

theorem sum_nodes_eq_sum_ends (nodes : ∀ i, Finset (P i)) (src tgt : E → ι)
    (xs : ∀ e, P (src e)) (xt : ∀ e, P (tgt e))
    (hmem_s : ∀ e, xs e ∈ nodes (src e)) (hmem_t : ∀ e, xt e ∈ nodes (tgt e))
    (hex : ∀ i, ∀ x ∈ nodes i, ∃ e,
      (⟨src e, xs e⟩ : Σ j, P j) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, P j) = ⟨i, x⟩)
    (huniq : ∀ i, ∀ x ∈ nodes i, ∀ e₁ e₂ : E ⊕ E,
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) e₁ = ⟨i, x⟩ →
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) e₂ = ⟨i, x⟩ → e₁ = e₂)
    (φ : ∀ j, P j → ℤ) (i : ι) :
    ∑ x ∈ nodes i, φ i x =
      (∑ e ∈ univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
        ∑ e ∈ univ.filter (fun e => src e = i), φ (src e) (xs e) := by
  classical
  set endOf : E ⊕ E → Σ j, P j :=
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) with hendOf
  set Φ : (Σ j, P j) → ℤ := fun y => φ y.1 y.2 with hΦ
  set S : Finset (E ⊕ E) := univ.filter (fun t => (endOf t).1 = i) with hS

  have hend_mem : ∀ t : E ⊕ E, (endOf t).2 ∈ nodes (endOf t).1 := by
    rintro (e | e)
    · exact hmem_s e
    · exact hmem_t e

  have hR : (∑ e ∈ univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
      ∑ e ∈ univ.filter (fun e => src e = i), φ (src e) (xs e) = ∑ t ∈ S, Φ (endOf t) := by
    rw [hS, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type, add_comm]
    rfl

  have hL : ∑ x ∈ nodes i, φ i x = ∑ y ∈ (nodes i).map (Function.Embedding.sigmaMk i), Φ y := by
    rw [Finset.sum_map]
    rfl

  have himage : S.image endOf = (nodes i).map (Function.Embedding.sigmaMk i) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_map, Function.Embedding.sigmaMk_apply, hS,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨cast (congrArg P ht) (endOf t).2, ?_, ?_⟩
      · have := hend_mem t
        revert this
        generalize endOf t = y at ht ⊢
        obtain ⟨j, x⟩ := y
        cases ht
        exact id
      · generalize endOf t = y at ht ⊢
        obtain ⟨j, x⟩ := y
        cases ht
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨e, he | he⟩ := hex i x hx
      · exact ⟨Sum.inl e, by simp [hendOf, congrArg Sigma.fst he], he⟩
      · exact ⟨Sum.inr e, by simp [hendOf, congrArg Sigma.fst he], he⟩
  have hinj : Set.InjOn endOf (S : Set (E ⊕ E)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.coe_filter, hS, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht₁ ht₂
    have hy : ∃ x ∈ nodes i, endOf t₁ = ⟨i, x⟩ := by
      have := hend_mem t₁
      revert this
      generalize endOf t₁ = y at ht₁ ⊢
      obtain ⟨j, x⟩ := y
      cases ht₁
      exact fun h => ⟨x, h, rfl⟩
    obtain ⟨x, hx, h₁⟩ := hy
    exact huniq i x hx t₁ t₂ h₁ (heq ▸ h₁)
  rw [hL, hR, ← himage, Finset.sum_image hinj]

end Nodes

end ChartPrincipalMomentEngine

namespace LC2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def mass : Divisor K F →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

theorem mass_eq_sum (D : Divisor K F) : mass D = D.sum fun _ k => k := by
  unfold mass; rw [Finsupp.liftAddHom_apply]; rfl

@[scoped simp] theorem mass_single (P : Place K F) (n : ℤ) : mass (Finsupp.single P n) = n := by
  rw [mass_eq_sum, Finsupp.sum_single_index rfl]

open Classical in

noncomputable def star {M : Type*} [GroupWithZero M] (a : Place K F → M) (P : Place K F) : M :=
  if a P = 0 then 1 else a P

theorem star_ne_zero {M : Type*} [GroupWithZero M] (a : Place K F → M) (P : Place K F) : star a P ≠ 0 := by
  classical
  unfold star; split_ifs with h
  · exact one_ne_zero
  · exact h

theorem star_of_ne_zero {M : Type*} [GroupWithZero M] (a : Place K F → M) {P : Place K F} (h : a P ≠ 0) :
    star a P = a P := by
  classical
  unfold star; rw [if_neg h]

theorem prod_zpow' {M : Type*} [CommGroupWithZero M] {α : Type*} [DecidableEq α] (s : Finset α) (f : α → M) (n : ℤ) :
    (∏ i ∈ s, f i) ^ n = ∏ i ∈ s, f i ^ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_zpow, ih]

theorem prod_star_add {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D E : Divisor K F) :
    ((D + E).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k) * (E.prod fun P k => star a P ^ k) :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun P b₁ b₂ => zpow_add₀ (star_ne_zero a P) b₁ b₂)

theorem prod_star_neg {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D : Divisor K F) :
    ((-D).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k)⁻¹ := by
  have h := prod_star_add a D (-D)
  rw [add_neg_cancel, Finsupp.prod_zero_index] at h
  have hne : (D.prod fun P k => star a P ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _ => zpow_ne_zero _ (star_ne_zero a P))
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem prod_star_sub {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D E : Divisor K F) :
    ((D - E).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k) * (E.prod fun P k => star a P ^ k)⁻¹ := by
  rw [sub_eq_add_neg, prod_star_add, prod_star_neg]

theorem prod_star_zsmul {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (n : ℤ) (D : Divisor K F) :
    ((n • D).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k) ^ n := by

  rw [Finsupp.prod_of_support_subset (n • D) Finsupp.support_smul (fun P k => star a P ^ k) (fun _ _ => zpow_zero _)]
  unfold Finsupp.prod
  classical
  rw [prod_zpow']
  refine Finset.prod_congr rfl (fun P _ => ?_)
  show star a P ^ (n • D) P = (star a P ^ (D P)) ^ n
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm, zpow_mul]

theorem prod_star_sum {M : Type*} [CommGroupWithZero M] (a : Place K F → M) {ι : Type*} (s : Finset ι)
    (D : ι → Divisor K F) :
    ((∑ i ∈ s, D i).prod fun P k => star a P ^ k) = ∏ i ∈ s, ((D i).prod fun P k => star a P ^ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Finsupp.prod_zero_index]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, prod_star_add, ih]

theorem prod_star_single {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (P : Place K F) (n : ℤ) :
    ((Finsupp.single P n).prod fun P k => star a P ^ k) = star a P ^ n := by
  rw [Finsupp.prod_single_index (zpow_zero _)]

theorem prod_star_eq_prod {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D : Divisor K F)
    (h : ∀ P ∈ D.support, a P ≠ 0) :
    (D.prod fun P k => star a P ^ k) = D.prod fun P k => a P ^ k :=
  Finset.prod_congr rfl (fun P hP => by simp only [star_of_ne_zero a (h P hP)])

end LC2
p2m_reactivate "P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent.LC2"

namespace RIPre2

open ChartPrincipalMomentEngine

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  [HasPrincipalDivisors L F]
  {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem sum_eq_ord_add_ord (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ maximalIdeal A → ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    {f : F} (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    (hN : ∀ P ∈ An.dom, N P = P.ord f)
    (hca : f ∈ Ca.integers) (hresa : Ca.residue ⟨f, hca⟩ ≠ 0)
    (hcb : f ∈ Cb.integers) (hresb : Cb.residue ⟨f, hcb⟩ ≠ 0) :
    (N.sum fun _ k => k) = xa.ord (Ca.residue ⟨f, hca⟩) + xb.ord (Cb.residue ⟨f, hcb⟩) := by
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := wide_of_isAlgClosed An hmod0
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₁
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hf0 : f ≠ 0 := by
    intro h0; apply hresa
    have : (⟨f, hca⟩ : Ca.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, Hb⟩ := hatt'
  obtain ⟨hzb, hxb, hslb⟩ := transfer_end Cb.residue xb hdom hp' Hb
  have heq : (algebraMap L F (1 : L))⁻¹ * f = f := by rw [map_one, inv_one, one_mul]
  have hhb : (algebraMap L F (1 : L))⁻¹ * f ∈ Cb.integers := by rw [heq]; exact hcb
  have hsub : (⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩ : Cb.integers) = ⟨f, hcb⟩ := Subtype.ext heq
  have hresb' : Cb.residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩ ≠ 0 := by rw [hsub]; exact hresb
  obtain ⟨hmass, -⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (rp Ca) xa hza hxa hsla (rp Cb) xb hzb hxb hslb ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩
      f hf0 hca hresa 1 one_ne_zero hhb hresb' N hNdom hN
  have hordb : xb.ord ((rp Cb).residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩) = xb.ord (Cb.residue ⟨f, hcb⟩) := by
    show xb.ord (Cb.residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩) = _
    rw [hsub]
  rw [hordb] at hmass
  exact hmass

end RIPre2
p2m_reactivate "P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent.LC2"

namespace RIPre2
theorem prod_zpow_eq_zpow_sum {M : Type*} [CommGroupWithZero M] {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ) (b : M) (hb : b ≠ 0) :
    ∏ i ∈ s, b ^ f i = b ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hb]
end RIPre2
p2m_reactivate "P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent.LC2"

namespace RIPre2

section PlaceLemma

theorem ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hle : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero h0
  unfold Place.ord
  have : WithZero.log (v.adicValuation f) ≤ WithZero.log 1 :=
    (WithZero.log_le_log hne one_ne_zero).mpr hle
  rw [WithZero.log_one] at this
  omega

theorem not_isUnit_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (hpos : 0 < v.ord f) : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem exists_not_mem (κ : Type*) [Field κ] [IsAlgClosed κ] (Fb' : Type*) [Field Fb'] [Algebra κ Fb']
    [IsCurveOver κ Fb'] [Algebra.EssFiniteType κ Fb'] (S : Finset (Place κ Fb')) : ∃ Q : Place κ Fb', Q ∉ S := by
  classical
  obtain ⟨t, ht, hfin, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := κ) (F := Fb')
  haveI := hfin
  set Cst := algebraMap κ Fb' with hCst
  have hCinj : Function.Injective Cst := (algebraMap κ Fb').injective
  have htc : ∀ d : κ, t - Cst d ≠ 0 := by
    intro d h; apply ht; rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap d

  have key : ∀ c c' : κ, c ≠ c' → ∃ v : Place κ Fb', 0 < v.ord (t - Cst c) ∨ 0 < v.ord (t - Cst c') := by
    intro c c' hcc

    have hx : (t - Cst c) / (t - Cst c') ∉ (algebraMap κ Fb').range := by
      rintro ⟨l, hl⟩
      have h1 : Cst l * (t - Cst c') = t - Cst c := by
        rw [show Cst l = algebraMap κ Fb' l from rfl, hl, div_mul_cancel₀ _ (htc c')]
      by_cases hl1 : l = 1
      · rw [hl1, map_one, one_mul, sub_right_inj] at h1
        exact hcc (hCinj h1).symm
      · apply ht
        have hl1' : Cst l - 1 ≠ 0 := by
          rw [sub_ne_zero, ← map_one Cst]; exact fun h => hl1 (hCinj h)
        have h2 : t = Cst ((l * c' - c) / (l - 1)) := by
          rw [map_div₀, map_sub Cst l 1, map_one, eq_div_iff hl1', map_sub, map_mul]
          linear_combination h1
        rw [h2]; exact isAlgebraic_algebraMap _
    obtain ⟨v, hv⟩ : ∃ v : Place κ Fb', v.ord ((t - Cst c) / (t - Cst c')) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hx (AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t ht hall)
    rw [div_eq_mul_inv, v.ord_mul (htc c) (inv_ne_zero (htc c')), v.ord_inv] at hv
    by_cases htv : t ∈ v.toValuationSubring
    · have ha : 0 ≤ v.ord (t - Cst c) := ord_nonneg_of_mem' v (sub_mem htv (v.algebraMap_mem' c))
      have hb : 0 ≤ v.ord (t - Cst c') := ord_nonneg_of_mem' v (sub_mem htv (v.algebraMap_mem' c'))
      refine ⟨v, ?_⟩
      rcases lt_trichotomy (v.ord (t - Cst c)) (v.ord (t - Cst c')) with h | h | h
      · right; omega
      · exact absurd (by rw [h]; ring) hv
      · left; omega
    ·
      exfalso
      have hti : t⁻¹ ∈ v.toValuationSubring := by
        rcases v.toValuationSubring.mem_or_inv_mem t with h | h
        · exact absurd h htv
        · exact h
      have ht0 : t ≠ 0 := fun h => htv (h ▸ zero_mem _)
      have hti_nu : ¬ IsUnit (⟨t⁻¹, hti⟩ : v.toValuationSubring) := by
        intro hu
        obtain ⟨w, hw⟩ := hu
        apply htv
        have hwv : ((w : v.toValuationSubring) : Fb') = t⁻¹ := congrArg Subtype.val hw
        have h := congrArg (fun z : v.toValuationSubring => (z : Fb')) w.inv_mul
        beta_reduce at h
        push_cast at h
        rw [hwv] at h
        have hval : (((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : Fb') = t := (mul_inv_eq_one₀ ht0).mp h
        rw [← hval]; exact ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).2

      have hunit : ∀ d : κ, ∃ hmem : (t - Cst d) * t⁻¹ ∈ v.toValuationSubring,
          IsUnit (⟨(t - Cst d) * t⁻¹, hmem⟩ : v.toValuationSubring) := by
        intro d
        have heq : (t - Cst d) * t⁻¹ = 1 - Cst d * t⁻¹ := by field_simp
        have hm : Cst d * t⁻¹ ∈ v.toValuationSubring := mul_mem (v.algebraMap_mem' d) hti
        have hmem : (t - Cst d) * t⁻¹ ∈ v.toValuationSubring := by rw [heq]; exact sub_mem (one_mem _) hm
        refine ⟨hmem, ?_⟩
        by_contra hnu
        have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
          (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have hmax2 : (⟨Cst d * t⁻¹, hm⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          have : (⟨Cst d * t⁻¹, hm⟩ : v.toValuationSubring) = ⟨Cst d, v.algebraMap_mem' d⟩ * ⟨t⁻¹, hti⟩ := rfl
          rw [this]
          intro hu
          exact hti_nu (isUnit_of_mul_isUnit_right hu)
        have : (1 : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
          have h1 : (1 : v.toValuationSubring) = ⟨_, hmem⟩ + ⟨Cst d * t⁻¹, hm⟩ := Subtype.ext (by push_cast; rw [heq]; ring)
          rw [h1]; exact add_mem hmax hmax2
        exact (maximalIdeal v.toValuationSubring).ne_top_iff_one.mp (Ideal.IsMaximal.ne_top inferInstance) this
      have hord : ∀ d : κ, v.ord (t - Cst d) = v.ord t := by
        intro d
        obtain ⟨hmem, hu⟩ := hunit d
        have h1 := v.ord_coe_unit hu.unit
        rw [IsUnit.unit_spec] at h1
        change v.ord ((t - Cst d) * t⁻¹) = 0 at h1
        rw [v.ord_mul (htc d) (inv_ne_zero ht0), v.ord_inv] at h1
        omega
      rw [hord c, hord c'] at hv
      exact hv (by ring)

  have mem_of_ord_nonneg : ∀ (v : Place κ Fb') (f : Fb'), f ≠ 0 → 0 ≤ v.ord f → f ∈ v.toValuationSubring := by
    intro v f hf0 hf
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hf0 hϖ
    rw [hw]
    lift v.ord f to ℕ using hf with n hn
    rw [zpow_natCast]
    exact mul_mem (w : v.toValuationSubring).2 (pow_mem ϖ.2 n)

  have disj : ∀ (c c' : κ) (v : Place κ Fb'), 0 < v.ord (t - Cst c) → 0 < v.ord (t - Cst c') → c = c' := by
    intro c c' v h1 h2
    by_contra hcc
    have hm1 : t - Cst c ∈ v.toValuationSubring := mem_of_ord_nonneg v _ (htc c) h1.le
    have hm2 : t - Cst c' ∈ v.toValuationSubring := mem_of_ord_nonneg v _ (htc c') h2.le
    have hx1 : (⟨_, hm1⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_of_ord_pos v hm1 h1)
    have hx2 : (⟨_, hm2⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_of_ord_pos v hm2 h2)
    have hd : (⟨Cst (c' - c), v.algebraMap_mem' (c' - c)⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
      have : (⟨Cst (c' - c), v.algebraMap_mem' (c' - c)⟩ : v.toValuationSubring) = ⟨_, hm1⟩ - ⟨_, hm2⟩ :=
        Subtype.ext (by push_cast; rw [map_sub]; ring)
      rw [this]; exact sub_mem hx1 hx2
    have hunit : IsUnit (⟨Cst (c' - c), v.algebraMap_mem' (c' - c)⟩ : v.toValuationSubring) := by
      have hne : c' - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcc)
      refine ⟨⟨⟨Cst (c' - c), v.algebraMap_mem' (c' - c)⟩, ⟨Cst (c' - c)⁻¹, v.algebraMap_mem' _⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext; push_cast; rw [← map_mul, mul_inv_cancel₀ hne, map_one]
      · apply Subtype.ext; push_cast; rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    exact ((IsLocalRing.mem_maximalIdeal _).mp hd) hunit

  haveI : Infinite κ := inferInstance
  let cs : Fin (S.card + 2) → κ := fun j => Infinite.natEmbedding κ j
  have hcs : Function.Injective cs := fun j j' h => Fin.ext ((Infinite.natEmbedding κ).injective h)
  let Z : Finset (Fin (S.card + 2)) := Finset.univ.filter (fun j => ∃ v : Place κ Fb', 0 < v.ord (t - Cst (cs j)))
  have hZ : ∀ j j' : Fin (S.card + 2), j ≠ j' → j ∈ Z ∨ j' ∈ Z := by
    intro j j' hjj
    obtain ⟨v, hv⟩ := key (cs j) (cs j') (fun h => hjj (hcs h))
    rcases hv with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, h⟩)
  have hcompl : (Finset.univ \ Z).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rcases hZ a b hab with h | h
    · exact (Finset.mem_sdiff.mp ha).2 h
    · exact (Finset.mem_sdiff.mp hb).2 h
  have hZcard : S.card + 1 ≤ Z.card := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun j => ∃ v : Place κ Fb', 0 < v.ord (t - Cst (cs j))) Finset.univ)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    change (Finset.univ \ Z).card + Z.card = S.card + 2 at h1
    omega
  have hZmem : ∀ j : ↥Z, ∃ v : Place κ Fb', 0 < v.ord (t - Cst (cs j)) := fun j => (Finset.mem_filter.mp j.2).2
  choose vz hvz using hZmem
  by_contra hall
  push_neg at hall
  have hinj : Function.Injective (fun j : ↥Z => (⟨vz j, hall (vz j)⟩ : ↥S)) := by
    intro j j' h
    have h' : vz j = vz j' := congrArg Subtype.val h
    apply Subtype.ext
    exact hcs (disj _ _ (vz j) (hvz j) (h' ▸ hvz j'))
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_coe] at this
  omega

end PlaceLemma
p2m_reactivate "P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent.LC2"

end RIPre2
p2m_reactivate "P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent.LC2"

set_option maxHeartbeats 1600000 in
theorem RIPrelude.exists_lift
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
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
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hdeg : ∀ i, Divisor.degree (Di i) = 0)
    (hred : NodalData.IsNodalPrincipal (K := IsLocalRing.ResidueField A) (Fbar := Fbar) src tgt xs xt
      (fun i => Finsupp.mapDomain (C i).placeMap (Di i))) :
    ∃ (f : F) (hf : f ≠ 0) (Gi' : Fin n → Divisor L F) (N : Fin m → Divisor L F),
      (∀ i, ∀ P ∈ (Gi' i).support, P ∈ (C i).dom) ∧
      (∀ i, Finsupp.mapDomain (C i).placeMap (Gi' i) = 0) ∧
      (∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom) ∧
      (∀ e, ((N e).sum fun _ k => k) = 0) ∧
      (∀ e, ∃ t ∈ IsLocalRing.maximalIdeal A,
        ((N e).prod fun P k => (P.evalAt (An e).param) ^ k) = 1 + ((t : A) : L)) ∧
      ∀ P : Place L F, (∑ i, Di i) P - P.ord f = (∑ i, Gi' i + ∑ e, N e) P := by
  classical
  obtain ⟨gbar, a, hg0, hEg, hval⟩ := hred
  haveI hκalg : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hchart : ∀ (P : Place L F) (i : Fin n), P ∈ (C i).dom → (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom := by
    intro P i hP
    rcases hcover P with ⟨i', _, huniq, han⟩ | ⟨e, _, _, hnoti⟩
    · obtain rfl := huniq i hP
      exact ⟨huniq, han⟩
    · exact absurd hP (hnoti i)
  have hann : ∀ (P : Place L F) (e₁ : Fin m), P ∈ (An e₁).dom → (∀ e', P ∈ (An e').dom → e' = e₁) ∧ ∀ i, P ∉ (C i).dom := by
    intro P e₁ hP
    rcases hcover P with ⟨i', hPi, _, han⟩ | ⟨e', _, huniq, hnoti⟩
    · exact absurd hP (han e₁)
    · obtain rfl := huniq e₁ hP
      exact ⟨huniq, hnoti⟩

  have hP0ex : ∀ i, ∃ P, P ∈ (C i).dom := by
    intro i
    obtain ⟨Q, hQ⟩ := RIPre2.exists_not_mem (ResidueField A) (Fbar i) (C i).nodes
    obtain ⟨T, hT, hT0, hT1, hTdisc, hTbij⟩ := hdisc i Q hQ
    obtain ⟨P, ⟨hP, -, -⟩, -⟩ := hTbij π hπ
    exact ⟨P, hP⟩
  choose P0 hP0 using hP0ex

  let absD : Fin n → Divisor L F := fun i => Finsupp.mapRange (fun k : ℤ => |k|) abs_zero (Di i)
  have habsD_supp : ∀ i, ∀ P ∈ (absD i).support, P ∈ (C i).dom := fun i P hP =>
    hdom i P (Finsupp.support_mapRange hP)
  have habsD_nonneg : ∀ i P, 0 ≤ absD i P := fun i P => by
    show 0 ≤ Finsupp.mapRange (fun k : ℤ => |k|) abs_zero (Di i) P
    rw [Finsupp.mapRange_apply]; exact abs_nonneg _
  have habsD_add : ∀ i P, 0 ≤ absD i P + Di i P := fun i P => by
    show 0 ≤ Finsupp.mapRange (fun k : ℤ => |k|) abs_zero (Di i) P + Di i P
    rw [Finsupp.mapRange_apply]
    have := neg_abs_le (Di i P); omega
  let dd : Fin n → ℤ := fun i => 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) + ((C i).nodes.card : ℤ)
  have hdd : ∀ i, 0 ≤ dd i := fun i => by positivity
  let Dpart : Fin n → Divisor L F := fun i => absD i + dd i • Finsupp.single (P0 i) 1
  have hDpart_supp : ∀ i, ∀ P ∈ (Dpart i).support, P ∈ (C i).dom := by
    intro i P hP
    rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
    · exact habsD_supp i P h
    · have := Finsupp.support_smul h
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at this
      rw [this]; exact hP0 i
  have hDpart_nonneg : ∀ i P, 0 ≤ Dpart i P := fun i P => by
    show 0 ≤ absD i P + (dd i • Finsupp.single (P0 i) (1 : ℤ)) P
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have := habsD_nonneg i P; have := hdd i
    split_ifs <;> nlinarith
  let Ds : Divisor L F := ∑ i, Dpart i
  have hDs : ∀ P ∈ Ds.support, ∃ i, P ∈ (C i).dom := by
    intro P hP
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hP)
    exact ⟨i, hDpart_supp i P hi⟩

  have hfilt : ∀ i, Ds.filter (fun P => P ∈ (C i).dom) = Dpart i := by
    intro i
    show Finsupp.filter (fun P => P ∈ (C i).dom) (∑ j, Dpart j) = Dpart i
    rw [show Finsupp.filter (fun P => P ∈ (C i).dom) (∑ j, Dpart j) = ∑ j, Finsupp.filter (fun P => P ∈ (C i).dom) (Dpart j)
      from map_sum (Finsupp.filterAddHom fun P => P ∈ (C i).dom) _ _]
    rw [Finset.sum_eq_single i]
    · rw [Finsupp.filter_eq_self_iff]
      intro P hP; by_contra h; exact h (hDpart_supp i P (Finsupp.mem_support_iff.mpr hP))
    · intro j _ hji
      rw [Finsupp.filter_eq_zero_iff]
      intro P hP
      by_contra h
      exact hji ((hchart P i hP).1 j (hDpart_supp j P (Finsupp.mem_support_iff.mpr h)))
    · intro h; exact absurd (Finset.mem_univ i) h

  have hmapD_nonneg : ∀ (i : Fin n) (D : Divisor L F), (∀ P, 0 ≤ D P) →
      ∀ v, 0 ≤ Finsupp.mapDomain (C i).placeMap D v := by
    intro i D hD v
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    exact Finset.sum_nonneg (fun P _ => by
      show 0 ≤ (Finsupp.single ((C i).placeMap P) (D P)) v
      rw [Finsupp.single_apply]; split_ifs
      · exact hD P
      · exact le_refl _)
  have hmap_single : ∀ i, Finsupp.mapDomain (C i).placeMap (Finsupp.single (P0 i) (1 : ℤ)) =
      Finsupp.single ((C i).placeMap (P0 i)) 1 := fun i => Finsupp.mapDomain_single
  have hDbar : ∀ i, Finsupp.mapDomain (C i).placeMap (Ds.filter (fun P => P ∈ (C i).dom)) =
      Finsupp.mapDomain (C i).placeMap (absD i) + dd i • Finsupp.single ((C i).placeMap (P0 i)) 1 := by
    intro i
    rw [hfilt i]
    show Finsupp.mapDomain.addMonoidHom (C i).placeMap (absD i + dd i • Finsupp.single (P0 i) 1) = _
    rw [map_add, map_zsmul]
    show Finsupp.mapDomain (C i).placeMap (absD i) + dd i • Finsupp.mapDomain (C i).placeMap (Finsupp.single (P0 i) 1) = _
    rw [hmap_single i]

  have hdegD : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (Ds.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)) := by
    intro i
    rw [hDbar i, ChartPrincipalMomentEngine.degree_eq_sum_of_isRational _ (fun Q _ => hratBar i Q),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.sum_single_index rfl]
    have h1 : 0 ≤ (Finsupp.mapDomain (C i).placeMap (absD i)).sum (fun _ k => k) := by
      rw [Finsupp.sum]
      exact Finset.sum_nonneg (fun v _ => hmapD_nonneg i (absD i) (habsD_nonneg i) v)
    show 2 * (genusFF (ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      (Finsupp.mapDomain (C i).placeMap (absD i)).sum (fun _ k => k) + (2 * (genusFF (ResidueField A) (Fbar i) : ℤ) + ((C i).nodes.card : ℤ))
    omega

  have hmemRR : ∀ i, gbar i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (Ds.filter fun P => P ∈ (C i).dom) :
      Divisor (IsLocalRing.ResidueField A) (Fbar i)) := by
    intro i
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    rw [← hEg i v, hDbar i, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have h1 : 0 ≤ Finsupp.mapDomain (C i).placeMap (absD i) v + Finsupp.mapDomain (C i).placeMap (Di i) v := by
      have := hmapD_nonneg i (absD i + Di i) (fun P => by rw [Finsupp.add_apply]; exact habsD_add i P) v
      rw [Finsupp.mapDomain_add, Finsupp.add_apply] at this
      exact this
    have h2 := hdd i
    split_ifs
    · linarith
    · linarith

  have hvalEq : ∀ e, (xs e).evalAt (gbar (src e)) = (xt e).evalAt (gbar (tgt e)) := by
    intro e
    obtain ⟨hs, ht⟩ := hval e
    have h1 : (xs e).evalAt (gbar (src e)) = (a e : ResidueField A) := by
      apply (algebraMap (ResidueField A) (xs e).ResidueField).injective
      rw [Place.algebraMap_evalAt (xs e) (hratBar _ _) hs.mem, hs.residue_eq]
    have h2 : (xt e).evalAt (gbar (tgt e)) = (a e : ResidueField A) := by
      apply (algebraMap (ResidueField A) (xt e).ResidueField).injective
      rw [Place.algebraMap_evalAt (xt e) (hratBar _ _) ht.mem, ht.residue_eq]
    rw [h1, h2]

  obtain ⟨-, hlift⟩ := AlgebraicCurve.SemistableCovering.exists_forall_residue_eq_of_forall_evalAt_eq_of_discFibres_of_rankOne A π hπ hπ0 hrk
    F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus Ds hDs hdegD
  obtain ⟨f, hfint, -, hfres⟩ := hlift gbar hmemRR hvalEq
  have hres0 : ∀ i, (C i).residue ⟨f, hfint i⟩ ≠ 0 := fun i => by rw [hfres i]; exact hg0 i
  have hf0 : f ≠ 0 := by
    have hn : 0 < n := by
      obtain ⟨P⟩ : Nonempty (Place L F) := by
        obtain ⟨t, ht, hfin, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := L) (F := F)
        haveI := hsep
        exact AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional L t ht hfin
      rcases hcover P with ⟨i, -⟩ | ⟨e, -⟩
      · exact i.pos
      · exact (src e).pos
    intro h0
    apply hres0 ⟨0, hn⟩
    have : (⟨f, hfint ⟨0, hn⟩⟩ : (C ⟨0, hn⟩).integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0

  have hmod0 : ∀ e, ((An e).modulus : L) ≠ 0 := fun e => (hpair e).2.2.1
  have hz0 : ∀ e, ∀ P ∈ (An e).dom, P.evalAt (An e).param ≠ 0 := fun e P hP => ((An e).mem_dom P hP).2.2.2.1
  have hkey : ∀ e, (((-(Df.filter (fun P => P ∈ (An e).dom))).sum fun _ k => k) = 0) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal A,
        ((-(Df.filter (fun P => P ∈ (An e).dom))).prod fun P k => (P.evalAt (An e).param) ^ k) = 1 + ((t : A) : L) := by
    intro e
    set N : Divisor L F := Df.filter (fun P => P ∈ (An e).dom) with hNdef
    have hNdom : ∀ P ∈ N.support, P ∈ (An e).dom := by
      intro P hP; rw [hNdef, Finsupp.support_filter] at hP; exact (Finset.mem_filter.mp hP).2
    have hN : ∀ P ∈ (An e).dom, N P = P.ord f := by
      intro P hP; rw [hNdef, Finsupp.filter_apply, if_pos hP, hDf P]

    obtain ⟨hvs, hvt⟩ := hval e
    have hσs : (xs e).ord ((C (src e)).residue ⟨f, hfint (src e)⟩) = 0 := by
      rw [hfres]; exact hvs.ord_eq_zero (a e).ne_zero
    have hσt : (xt e).ord ((C (tgt e)).residue ⟨f, hfint (tgt e)⟩) = 0 := by
      rw [hfres]; exact hvt.ord_eq_zero (a e).ne_zero

    have hmassN : (N.sum fun _ k => k) = 0 := by
      rw [RIPre2.sum_eq_ord_add_ord hrk (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e) (C (src e)) (xs e) (hatt e).1
        (C (tgt e)) (xt e) (hatt e).2 N hNdom hN (hfint (src e)) (hres0 (src e)) (hfint (tgt e)) (hres0 (tgt e)), hσs, hσt, add_zero]
    have hmassneg : ((-N).sum fun _ k => k) = 0 := by
      rw [← LC2.mass_eq_sum, map_neg, LC2.mass_eq_sum, hmassN, neg_zero]
    refine ⟨hmassneg, ?_⟩

    have heq1 : (algebraMap L F (1 : L))⁻¹ * f = f := by rw [map_one, inv_one, one_mul]
    have hhb : (algebraMap L F (1 : L))⁻¹ * f ∈ (C (tgt e)).integers := by rw [heq1]; exact hfint (tgt e)
    have hsub : (⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩ : (C (tgt e)).integers) = ⟨f, hfint (tgt e)⟩ := Subtype.ext heq1
    have hresb' : (C (tgt e)).residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩ ≠ 0 := by rw [hsub]; exact hres0 (tgt e)
    obtain ⟨hu, -, hlam⟩ :=
      AlgebraicCurve.Annulus.exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached A hrk
        (hratBar (src e)) (hratBar (tgt e)) (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e)
        (C (src e)) (xs e) (hatt e).1 (C (tgt e)) (xt e) (hatt e).2
        f hf0 (hfint (src e)) (hres0 (src e)) 1 one_ne_zero hhb hresb' N hNdom hN
    have hσt' : (xt e).ord ((C (tgt e)).residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩) = 0 := by rw [hsub]; exact hσt
    have hlamA : (xs e).evalAt ((C (src e)).residue ⟨f, hfint (src e)⟩ *
        ((C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩) ^ (-((xs e).ord ((C (src e)).residue ⟨f, hfint (src e)⟩)))) =
        (a e : ResidueField A) := by
      rw [hσs, neg_zero, zpow_zero, mul_one, hfres]
      apply (algebraMap (ResidueField A) (xs e).ResidueField).injective
      rw [Place.algebraMap_evalAt (xs e) (hratBar _ _) hvs.mem, hvs.residue_eq]
    have hlamB : (xt e).evalAt ((C (tgt e)).residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩ *
        ((C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩) ^ (-((xt e).ord ((C (tgt e)).residue ⟨(algebraMap L F (1 : L))⁻¹ * f, hhb⟩)))) =
        (a e : ResidueField A) := by
      rw [hσt', neg_zero, zpow_zero, mul_one, hsub, hfres]
      apply (algebraMap (ResidueField A) (xt e).ResidueField).injective
      rw [Place.algebraMap_evalAt (xt e) (hratBar _ _) hvt.mem, hvt.residue_eq]
    rw [hlamA, hlamB] at hlam
    have hres1 : IsLocalRing.residue A ⟨_, hu⟩ = 1 := by
      have ha0 : ((a e : ResidueField A)) ≠ 0 := (a e).ne_zero
      exact (mul_eq_right₀ ha0).mp hlam

    have hsign : (N.prod fun P k => (-(P.evalAt (An e).param)) ^ k) = N.prod fun P k => (P.evalAt (An e).param) ^ k := by
      rw [show (N.prod fun P k => (-(P.evalAt (An e).param)) ^ k) =
          (N.prod fun P k => (-1 : L) ^ k) * N.prod fun P k => (P.evalAt (An e).param) ^ k from by
            rw [← Finsupp.prod_mul]; refine Finset.prod_congr rfl (fun P _ => ?_)
            show (-(P.evalAt (An e).param)) ^ (N P) = (-1 : L) ^ (N P) * (P.evalAt (An e).param) ^ (N P)
            rw [← mul_zpow, neg_one_mul]]
      have : (N.prod fun P k => (-1 : L) ^ k) = 1 := by
        unfold Finsupp.prod
        rw [RIPre2.prod_zpow_eq_zpow_sum _ _ (-1 : L) (neg_ne_zero.mpr one_ne_zero),
          show (∑ P ∈ N.support, N P) = N.sum (fun _ k => k) from rfl, hmassN, zpow_zero]
      rw [this, one_mul]
    have hval' : (1 : L)⁻¹ * ((An e).modulus : L) ^ ((xs e).ord ((C (src e)).residue ⟨f, hfint (src e)⟩) - (N.sum fun _ k => k)) *
        (N.prod fun P k => (-(P.evalAt (An e).param)) ^ k) = N.prod fun P k => (P.evalAt (An e).param) ^ k := by
      rw [hσs, hmassN, sub_self, zpow_zero, inv_one, one_mul, one_mul, hsign]
    have hvA : (N.prod fun P k => (P.evalAt (An e).param) ^ k) ∈ A := hval' ▸ hu
    have hvres : IsLocalRing.residue A ⟨_, hvA⟩ = 1 := by
      have : (⟨_, hvA⟩ : A) = ⟨_, hu⟩ := Subtype.ext hval'.symm
      rw [this]; exact hres1

    have hvunit : IsUnit (⟨_, hvA⟩ : A) := by
      by_contra hnu
      have := (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      rw [hvres] at this; exact one_ne_zero this
    obtain ⟨V, hV⟩ := hvunit
    have hneg : ((-N).prod fun P k => (P.evalAt (An e).param) ^ k) = ((V⁻¹ : Aˣ) : A) := by
      rw [← LC2.prod_star_eq_prod _ (-N) (fun P hP => hz0 e P (hNdom P (by rwa [Finsupp.support_neg] at hP))),
        LC2.prod_star_neg, LC2.prod_star_eq_prod _ N (fun P hP => hz0 e P (hNdom P hP))]
      have h1 : (((V : Aˣ) : A) : L) = N.prod fun P k => (P.evalAt (An e).param) ^ k := by rw [hV]
      rw [← h1]
      symm; apply eq_inv_of_mul_eq_one_left
      rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl
    refine ⟨((V⁻¹ : Aˣ) : A) - 1, ?_, ?_⟩
    · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
      have h2 : IsLocalRing.residue A ((V : Aˣ) : A) = 1 := by rw [hV]; exact hvres
      have h3 := congrArg (IsLocalRing.residue A) V.inv_mul
      rw [map_mul, map_one, h2, mul_one] at h3
      exact h3
    · rw [hneg]; push_cast; ring

  refine ⟨f, hf0, fun i => Di i - Df.filter (fun P => P ∈ (C i).dom), fun e => -(Df.filter (fun P => P ∈ (An e).dom)),
    fun i => RIPre.support_sub_filter_subset A (C i) (Di i) Df (hdom i),
    fun i => RIPre.mapDomain_placeMap_sub_filter_eq_zero A (C i) (Di i) (hdom i) (gbar i) (hEg i) f (hfint i) (hfres i) (hg0 i) Df hDf,
    fun e => RIPre.support_neg_filter_subset (An e).dom Df, ?_, ?_, ?_⟩
  ·
    intro e
    exact (hkey e).1
  ·
    intro e
    exact (hkey e).2
  · intro P
    rw [← hDf P]
    exact RIPre.sum_sub_eq_sum_sub_filter_add_sum_neg_filter A C An hcover Di hdom Df P

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

namespace S1MDAsm

theorem valuationRing_of_range_eq_inter {L : Type u} [Field L] (A : ValuationSubring L) {A₁ : Type u} [CommRing A₁]
    (ι₁ : A₁ →+* A) (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    haveI := Function.Injective.isDomain ι₁ hι₁; ValuationRing A₁ := by
  haveI := Function.Injective.isDomain ι₁ hι₁
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  have ha : ((ι₁ a : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨a, rfl⟩
  have hb : ((ι₁ b : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨b, rfl⟩
  by_cases hb0 : b = 0
  · exact ⟨0, Or.inl (by simp [hb0])⟩
  by_cases ha0 : a = 0
  · exact ⟨0, Or.inr (by simp [ha0])⟩
  rcases A.mem_or_inv_mem (((ι₁ b : A) : L) / ((ι₁ a : A) : L)) with h | h
  · have hK : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ (K₁ : Set L) := K₁.div_mem hb.2 ha.2
    obtain ⟨c, hc⟩ : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inl ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    have haL : ((ι₁ a : A) : L) ≠ 0 := by
      intro h; apply ha0; apply hι₁; simpa using h
    rw [hc]; field_simp
  · rw [inv_div] at h
    have hK : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ (K₁ : Set L) := K₁.div_mem ha.2 hb.2
    obtain ⟨c, hc⟩ : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inr ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    have hbL : ((ι₁ b : A) : L) ≠ 0 := by
      intro h; apply hb0; apply hι₁; simpa using h
    rw [hc]; field_simp

end S1MDAsm
p2m_reactivate "P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent.LC2"

open S1MDAsm in
set_option linter.unusedVariables false in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
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
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hdeg : ∀ i, Divisor.degree (Di i) = 0)
    (hred : NodalData.IsNodalPrincipal (K := IsLocalRing.ResidueField A) (Fbar := Fbar) src tgt xs xt
      (fun i => Finsupp.mapDomain (C i).placeMap (Di i)))
    (hkD : (k : ℤ) • (∑ i, Di i) ∈ Divisor.principal (K := L) (F := F)) :
    (∑ i, Di i) ∈ Divisor.principal (K := L) (F := F) := by
  classical

  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; rw [h0, Nat.cast_zero] at hk; exact not_isUnit_zero hk
    · exact h0
  haveI hdomA₀ : IsDomain D.A₀ := Function.Injective.isDomain D.ι D.ι_injective
  have hdim : Ring.KrullDimLE 1 D.A₀ := by
    haveI : ValuationRing D.A₀ := valuationRing_of_range_eq_inter A D.ι D.ι_injective D.K₀ D.range_ι
    haveI : IsPrincipalIdealRing D.A₀ := inferInstance
    exact Ring.KrullDimLE.mk₁' (fun I hI hp => IsPrime.to_maximal_ideal (hpi := hp) hI)

  obtain ⟨f, hf0, Gi', N, hGi', hred', hN, hmass, hbalN, hGf⟩ :=
    RIPrelude.exists_lift A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover
      hdisc hgenus Di hdom hdeg hred
  set G' : Divisor L F := ∑ i, Gi' i + ∑ e, N e with hG'def

  obtain ⟨g₀, hg₀0, hg₀div⟩ := Divisor.mem_principal.mp hkD
  have hgenus' : genusFF L F + Fintype.card (Fin n) =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card (Fin m) + 1 := by
    simpa only [Fintype.card_fin] using hgenus
  set g : F := g₀ / f ^ k with hgdef
  have hg0 : g ≠ 0 := div_ne_zero hg₀0 (pow_ne_zero _ hf0)
  have hkG' : ∀ P : Place L F, P.ord g = (k : ℤ) * G' P := by
    intro P
    rw [hgdef, div_eq_mul_inv, P.ord_mul hg₀0 (inv_ne_zero (pow_ne_zero _ hf0)), P.ord_inv, ← zpow_natCast,
      P.ord_zpow, ← hg₀div P, Finsupp.smul_apply, smul_eq_mul, hG'def, ← hGf P]
    ring

  obtain ⟨r, U, h, hU, hh, hdiv, hcoc, hv1, hv2⟩ :=
    AlgebraicCurve.exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus M
      Gi' hGi' hred' N hN hmass hbalN
  rw [← hG'def] at hdiv hv1 hv2

  obtain ⟨c, hc0, hcunit, hcslope⟩ :=
    AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus' M
      G' k hkpos g hg0 hkG' r U h hU hh hdiv hcoc

  have hΛ : ∀ s : F, ∃ Λ : Finset L, s ∈ Subfield.closure ((D.F₀ : Set F) ∪ (algebraMap L F) '' (↑Λ : Set L)) :=
    fun s => AlgebraicCurve.SemistableModel.Descent.exists_finset_mem_subfieldClosure_union_image_algebraMap M D s
  choose Λf hΛf using hΛ
  let S' : Finset F := insert g (Finset.univ.image h)
  let Λ : Finset L := S'.biUnion Λf ∪ Finset.univ.image c

  obtain ⟨K₁, hfin, hΛK, hnoeth, hhens, j₁, ι₁, hjloc, hι₁loc, hι₁inj, hcomp, hres, hpin, hdvr⟩ :=
    ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
      A D.A₀ hdim D.ι D.ι_injective D.K₀ D.range_ι D.residue_comp_surjective Λ
  have range_ι₁ : Set.range (fun a : ↥(A.comap (algebraMap K₁ L)) => ((ι₁ a : A) : L)) =
      (A : Set L) ∩ ((K₁.toSubfield : Subfield L) : Set L) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨(ι₁ a).2, ?_⟩
      show ((ι₁ a : A) : L) ∈ (K₁.toSubfield : Subfield L)
      rw [hpin a]
      exact (a : K₁).2
    · rintro ⟨hyA, hyK⟩
      have hk : (⟨y, hyK⟩ : K₁) ∈ A.comap (algebraMap K₁ L) := by
        rw [ValuationSubring.mem_comap]; exact hyA
      refine ⟨⟨⟨y, hyK⟩, hk⟩, ?_⟩
      show ((ι₁ ⟨⟨y, hyK⟩, hk⟩ : A) : L) = y
      rw [hpin]; rfl

  haveI := hι₁loc; haveI := hjloc; haveI := hnoeth; haveI := hhens; haveI := hfin
  obtain ⟨X₁, hX₁, f₁, hprop, hflat, e₁, he₁, hnorm₁, F₁, φ₁, hF₀, hK₁, halg, hgen, hcompat⟩ :=
    AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
      M D ↥(A.comap (algebraMap K₁ L)) j₁ ι₁ hι₁inj hcomp K₁.toSubfield range_ι₁
  haveI := hX₁; haveI := hprop; haveI := hflat

  have hS'F₁ : ∀ s ∈ S', s ∈ F₁ := by
    intro s hs
    refine (Subfield.closure_le.mpr ?_) (hΛf s)
    rintro z (hz | ⟨x, hx, rfl⟩)
    · exact hF₀ hz
    · refine hK₁ x ?_
      have hxΛ : x ∈ (↑Λ : Set L) := by
        simp only [Λ, Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
        exact Or.inl ⟨s, hs, hx⟩
      exact hΛK hxΛ
  have hgF₁ : g ∈ F₁ := hS'F₁ g (Finset.mem_insert_self _ _)
  have hhF₁ : ∀ a, h a ∈ F₁ := fun a =>
    hS'F₁ (h a) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem h (Finset.mem_univ a)))
  have hcK₁ : ∀ i, c i ∈ K₁ := fun i => hΛK (by
    simp only [Λ, Finset.coe_union, Set.mem_union, Finset.coe_image]
    exact Or.inr ⟨i, Finset.mem_univ i, rfl⟩)

  obtain ⟨c₀, hc₀F₁, g₁, r₁, U₁, h₁, hc₀, hg₁def, hg₁0, halgcl, hk₁, hU₁, hh₁, hdiv₁, hcoc₁, hconn₁⟩ :=
    AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus' M D
      k hk G' g hg0 hkG' r U h hU hh hdiv hcoc hv1 hv2 c hc0 hcunit hcslope
      K₁ j₁ ι₁ hι₁inj hcomp hres hpin hdvr X₁ f₁ e₁ he₁ hnorm₁ F₁ φ₁ hF₀ hK₁ halg ⟨hgen, hcompat⟩ hgF₁ hhF₁ hcK₁
  haveI := halgcl

  have hC3 := AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
    f₁ hnorm₁ k hk₁ g₁ hg₁0 r₁ U₁ hU₁ h₁ hh₁ hdiv₁ hcoc₁ hconn₁
  obtain ⟨hfinπ, hetπ, s₀, hs₀⟩ := hC3
  haveI := hfinπ; haveI := hetπ

  obtain ⟨s, hs, -⟩ :=
    AlgebraicGeometry.exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
      f₁ _ s₀ hs₀

  obtain ⟨f₀, hf₀⟩ := AlgebraicGeometry.exists_pow_eq_of_section_fromNormalization_kummer k g₁ hg₁0 s hs

  let fF : F := ((φ₁.symm f₀ : F₁) : F)
  have hfF : fF ^ k = c₀ • g := by
    have h1 : φ₁.symm (f₀ ^ k) = φ₁.symm g₁ := by rw [hf₀]
    rw [map_pow, hg₁def, RingEquiv.symm_apply_apply] at h1
    have h2 := congrArg (fun x : F₁ => (x : F)) h1
    simpa using h2

  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c₀ hkpos
  have hd0 : d ≠ 0 := by
    intro h0; apply hc₀; rw [← hd, h0, zero_pow hkpos.ne']
  let uF : F := fF / algebraMap L F d
  have huF : uF ^ k = g := by
    have hdF : algebraMap L F d ≠ 0 := (map_ne_zero _).mpr hd0
    show (fF / algebraMap L F d) ^ k = g
    rw [div_pow, hfF, ← map_pow, hd, Algebra.smul_def]
    have hc₀F : algebraMap L F c₀ ≠ 0 := (map_ne_zero _).mpr hc₀
    field_simp
  have huF0 : uF ≠ 0 := by
    intro h0; apply hg0; rw [← huF, h0, zero_pow hkpos.ne']

  have hG'u : ∀ P : Place L F, G' P = P.ord uF := by
    intro P
    have h1 := hkG' P
    rw [← huF] at h1
    have h2 : P.ord (uF ^ k) = (k : ℤ) * P.ord uF := by
      rw [← zpow_natCast, P.ord_zpow]
    rw [h2] at h1
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
    exact (mul_left_cancel₀ hk0 h1).symm
  refine Divisor.mem_principal.mpr ⟨uF * f, mul_ne_zero huF0 hf0, fun P => ?_⟩
  rw [P.ord_mul huF0 hf0, ← hG'u P, ← hGf P, sub_add_cancel]

end S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent
end P2MW
export P2MW.S_AlgebraicCurve_sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent (solution)
