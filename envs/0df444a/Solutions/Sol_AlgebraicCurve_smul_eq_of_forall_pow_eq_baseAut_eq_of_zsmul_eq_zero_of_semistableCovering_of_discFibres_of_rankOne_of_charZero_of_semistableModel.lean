-- Prove2me | solution 1 for AlgebraicCurve.smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6ab627ad-29e3-5235-a5bd-5d45dba3684e

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
import Theorems.Thm_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
import Theorems.Thm_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
import Theorems.Thm_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk"
p2m_attr_erase "simp" "ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve

namespace P2mWs20RootValue

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem mem_and_isUnit_of_pow_eq {x : L} {N : ℕ} (hN : N ≠ 0) {v : A} (hv : IsUnit v) (hx : x ^ N = (v : L)) :
    ∃ hxA : x ∈ A, IsUnit (⟨x, hxA⟩ : A) := by
  have hv1 : A.valuation (v : L) = 1 := (A.valuation_eq_one_iff v).mp hv
  have hx1 : A.valuation x = 1 := by
    have h : A.valuation x ^ N = 1 := by rw [← map_pow, hx, hv1]
    exact (pow_eq_one_iff.mp h).resolve_right hN
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx1.le
  exact ⟨hxA, (A.valuation_eq_one_iff ⟨x, hxA⟩).mpr hx1⟩

end P2mWs20RootValue

namespace ValuationSubring p2m_export "ValuationSubring" "neg_mem ext mk valuation_le_one_iff valuation valuation_eq_one_iff exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne" end ValuationSubring
p2m_open_scoped "ValuationSubring" in
open P2mWs20RootValue IsLocalRing in

theorem ValuationSubring.exists_apply_eq_mul_one_add_of_pow_eq_mul_pow_of_forall_apply_eq_self
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ)
    (π : L) (hπ0 : π ≠ 0)
    (σ : L ≃+* L) (hσA : ∀ a : L, a ∈ A ↔ σ a ∈ A)
    (hσres : ∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a)
    (hfix : ∀ r : L, r ^ (ℓ ^ k) = π → σ r = r)
    (c : L) (v : A) (hv : IsUnit v) (j : ℕ) (hc : c ^ (ℓ ^ k) = (v : L) * π ^ j) :
    ∃ t : A, t ∈ IsLocalRing.maximalIdeal A ∧ σ c = c * (1 + (t : L)) := by
  have hN : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k

  obtain ⟨π₀, hπ₀⟩ := IsAlgClosed.exists_pow_nat_eq π hN
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hπ₀
    exact hπ0 hπ₀.symm
  have hσπ₀ : σ π₀ = π₀ := hfix π₀ hπ₀

  set v₀ : L := c * (π₀ ^ j)⁻¹ with hv₀def
  have hcv₀ : c = π₀ ^ j * v₀ := by
    rw [hv₀def, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hπ₀0), mul_one]
  have hv₀pow : v₀ ^ (ℓ ^ k) = (v : L) := by
    rw [hv₀def, mul_pow, inv_pow, ← pow_mul, mul_comm j, pow_mul, hπ₀, hc, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero j hπ0), mul_one]
  obtain ⟨hv₀A, hv₀u⟩ := mem_and_isUnit_of_pow_eq A hN.ne' hv hv₀pow
  have hv₀0 : v₀ ≠ 0 := fun h => by
    rw [h, zero_pow hN.ne'] at hv₀pow
    exact hv.ne_zero (Subtype.ext hv₀pow.symm)

  have hσv₀A : σ v₀ ∈ A := (hσA v₀).mp hv₀A
  have hres : residue A ⟨σ v₀, hσv₀A⟩ = residue A ⟨v₀, hv₀A⟩ := hσres ⟨v₀, hv₀A⟩ hσv₀A
  have hdiff : (⟨σ v₀, hσv₀A⟩ : A) - ⟨v₀, hv₀A⟩ ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.eq]
    exact hres

  obtain ⟨w, hw⟩ := hv₀u
  refine ⟨(⟨σ v₀, hσv₀A⟩ - ⟨v₀, hv₀A⟩) * ↑w⁻¹, Ideal.mul_mem_right _ _ hdiff, ?_⟩
  have hwv : ((w⁻¹ : Aˣ) : A) * (⟨v₀, hv₀A⟩ : A) = 1 := by rw [← hw, Units.inv_mul]
  have hwv' : (((w⁻¹ : Aˣ) : A) : L) * v₀ = 1 := by
    have := congrArg (fun x : A => (x : L)) hwv
    simpa using this
  have hwinv : (((w⁻¹ : Aˣ) : A) : L) = v₀⁻¹ := eq_inv_of_mul_eq_one_left hwv'
  calc σ c = π₀ ^ j * σ v₀ := by rw [hcv₀, map_mul, map_pow, hσπ₀]
    _ = π₀ ^ j * v₀ * (1 + (σ v₀ - v₀) * v₀⁻¹) := by
        have h1 : v₀ * (1 + (σ v₀ - v₀) * v₀⁻¹) = σ v₀ := by
          rw [mul_add, mul_one, ← mul_assoc, mul_comm v₀ (σ v₀ - v₀), mul_assoc, mul_inv_cancel₀ hv₀0, mul_one,
            add_sub_cancel]
        rw [mul_assoc, h1]
    _ = c * (1 + (((⟨σ v₀, hσv₀A⟩ - ⟨v₀, hv₀A⟩) * ↑w⁻¹ : A) : L)) := by
        rw [← hcv₀]
        congr 2
        push_cast
        rw [hwinv]

namespace KLB

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem ann_eq_of_evalAt_eq (An : Annulus A F) (P Q : Place L F) (hP : P ∈ An.dom) (hQ : Q ∈ An.dom)
    (h : P.evalAt An.param = Q.evalAt An.param) : P = Q := by
  obtain ⟨-, -, ⟨hA, hmax⟩, hne, hmod⟩ := An.mem_dom P hP
  obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨P.evalAt An.param, hA⟩ hmax hne hmod
  rw [huniq P ⟨hP, rfl⟩, huniq Q ⟨hQ, h.symm⟩]

theorem ann_evalAt_smul (An : Annulus A F) (z : F) (s : SemilinearAut L F)
    (hdom : ∀ P ∈ An.dom, s • P ∈ An.dom) (hpar : s • z = z)
    (P : Place L F) (hP : P ∈ An.dom) :
    (s • P).evalAt z = SemilinearAut.baseAut s (P.evalAt z) := by
  have h1 : (s • P).IsRational := (An.mem_dom (s • P) (hdom P hP)).1
  have h0 : P.IsRational := (An.mem_dom P hP).1
  have := AlgebraicCurve.Place.evalAt_smul_smul_eq_baseAut_evalAt s P h0 h1 z
  rwa [hpar] at this

theorem annulus_shift (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (An : Annulus A F) (z' : F) (s : SemilinearAut L F)
    (hA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) (hsπ : SemilinearAut.baseAut s (π : L) = (π : L))
    (hdom : ∀ P ∈ An.dom, s • P ∈ An.dom) (hpar : s • An.param = An.param) (hpar' : s • z' = z')
    (Q : Place L F) (hQ : Q ∈ An.dom) :
    s • Q ∈ An.dom ∧
      (s • Q).evalAt An.param = SemilinearAut.baseAut s (Q.evalAt An.param) ∧
      (s • Q).evalAt z' = SemilinearAut.baseAut s (Q.evalAt z') ∧
      (∃ u : Aˣ, SemilinearAut.baseAut s (Q.evalAt An.param) = ((u : A) : L) * Q.evalAt An.param) ∧
      (∀ Q' ∈ An.dom,
        Q'.evalAt An.param = SemilinearAut.baseAut s (Q.evalAt An.param) → s • Q = Q') ∧
      (∀ Q' : Place L F,
        s • ((Finsupp.single Q' 1 : Divisor L F) - Finsupp.single Q 1) =
          (Finsupp.single (s • Q') 1 : Divisor L F) - Finsupp.single (s • Q) 1) := by
  have hz : (s • Q).evalAt An.param = SemilinearAut.baseAut s (Q.evalAt An.param) :=
    ann_evalAt_smul An An.param s hdom hpar Q hQ
  refine ⟨hdom Q hQ, hz, ann_evalAt_smul An z' s hdom hpar' Q hQ, ?_, ?_, ?_⟩
  · have hne : Q.evalAt An.param ≠ 0 := (An.mem_dom Q hQ).2.2.2.1
    obtain ⟨u, hu⟩ := ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne A π hπ hπ0 hrk
      (SemilinearAut.baseAut s) hA hsπ (Q.evalAt An.param) hne
    exact ⟨u, hu⟩
  · intro Q' hQ' hval
    exact ann_eq_of_evalAt_eq An (s • Q) Q' (hdom Q hQ) hQ' (by rw [hz, hval])
  · intro Q'
    rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]

end KLB

namespace KLB

open Classical in

theorem core {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))
    (An : Fin m → Annulus A F)
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (g : SemilinearAut L F)
    (hgA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A)
    (hgπ : SemilinearAut.baseAut g (π : L) = (π : L))
    (hgres : ∀ (a : A) (h : SemilinearAut.baseAut g (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut g (a : L), h⟩ = IsLocalRing.residue A a)
    (hgC : ∀ i, ∀ P ∈ (C i).dom, g • P ∈ (C i).dom)
    (hgAn : ∀ e, ∀ P ∈ (An e).dom, g • P ∈ (An e).dom)
    (hgpar : ∀ e, g • (An e).param = (An e).param)
    (hgpl : ∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = (C i).placeMap P)
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ)
    (hfix : ∀ r : L, r ^ (ℓ ^ k) = (π : L) → SemilinearAut.baseAut g r = r)
    (hrep : ∀ c : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • c = 0 →
      ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
        Pic0.mk ⟨D, hD⟩ = c ∧
        ∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (v : Aˣ) (j : ℕ),
            (P.evalAt (An e).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L) ^ j)
    (htf : ∀ (Gi : Fin n → Divisor L F), (∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom) →
      (∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0) →
      ∀ (ι : Type) [Fintype ι] (e : ι → Fin m) (nq : ι → ℤ) (Q : ι → Fin 4 → Place L F),
      (∀ j l, Q j l ∈ (An (e j)).dom) →
      (∀ j, ∃ u : Aˣ,
        (Q j 0).evalAt (An (e j)).param = ((u : A) : L) * (Q j 2).evalAt (An (e j)).param) →
      (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
        (Q j 0).evalAt (An (e j)).param * (Q j 1).evalAt (An (e j)).param =
          (Q j 2).evalAt (An (e j)).param * (Q j 3).evalAt (An (e j)).param * (1 + ((t : A) : L))) →
      (((ℓ ^ k : ℕ) : ℤ) • (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) ∈
        Divisor.principal (K := L) (F := F)) →
      (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) ∈
        Divisor.principal (K := L) (F := F)) :
    ∀ c : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • c = 0 → g • c = c := by
  intro c hc
  obtain ⟨D, hD, rfl, hsupp⟩ := hrep c hc

  have hND : ((ℓ ^ k : ℕ) : ℤ) • D ∈ Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk (((ℓ ^ k : ℕ) : ℤ) • (⟨D, hD⟩ : Divisor.degZero (K := L) (F := F))) = 0 := by
      rw [Pic0.mk, QuotientAddGroup.mk_zsmul]
      exact hc
    rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    simpa using h1

  suffices hpr : g • D - D ∈ Divisor.principal (K := L) (F := F) by
    rw [SemilinearAut.pic0_smul_mk, Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have : -(g • D) + D ∈ Divisor.principal (K := L) (F := F) := by
      rw [neg_add_eq_sub, ← neg_sub]
      exact neg_mem hpr
    simpa [SemilinearAut.coe_degZeroSMulHom] using this

  set s := D.support with hs
  let δ : Place L F → Divisor L F := fun P => Finsupp.single (g • P) (D P) - Finsupp.single P (D P)
  have hδ : g • D - D = ∑ P ∈ s, δ P := by
    have hDsum : D = ∑ P ∈ s, Finsupp.single P (D P) := (Finsupp.sum_single D).symm
    conv_lhs => rw [hDsum]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [SemilinearAut.smul_single]

  let isC : Place L F → Prop := fun P => ∃ i, P ∈ (C i).dom
  have hann : ∀ P ∈ s.filter (fun P => ¬ isC P), ∃ e, P ∈ (An e).dom ∧ ∃ (v : Aˣ) (j : ℕ),
      (P.evalAt (An e).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L) ^ j := by
    intro P hP
    rw [Finset.mem_filter] at hP
    rcases hsupp P hP.1 with h | h
    · exact absurd h hP.2
    · exact h

  let Gi : Fin n → Divisor L F := fun i => ∑ P ∈ s.filter (fun P => P ∈ (C i).dom), δ P
  have hGi : ∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom := by
    intro i P hP
    have hP' := Finsupp.support_finsetSum (s := s.filter (fun P => P ∈ (C i).dom)) (f := fun P => δ P) hP
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hP'
    obtain ⟨R, ⟨-, hR⟩, hPR⟩ := hP'
    have hsub : (δ R).support ⊆ {g • R, R} := by
      intro X hX
      have := Finsupp.support_sub (f := Finsupp.single (g • R) (D R)) (g := Finsupp.single R (D R)) hX
      simp only [Finset.mem_union] at this
      rcases this with h1 | h1
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)))
      · exact Finset.mem_insert.mpr (Or.inr (Finsupp.support_single_subset h1))
    rcases Finset.mem_insert.mp (hsub hPR) with h1 | h1
    · rw [h1]; exact hgC i R hR
    · rw [Finset.mem_singleton] at h1; rw [h1]; exact hR
  have hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0 := by
    intro i
    show Finsupp.mapDomain.addMonoidHom (C i).placeMap (∑ P ∈ s.filter (fun P => P ∈ (C i).dom), δ P) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero (fun P hP => ?_)
    rw [Finset.mem_filter] at hP
    show Finsupp.mapDomain (C i).placeMap (Finsupp.single (g • P) (D P) - Finsupp.single P (D P)) = 0
    have : Finsupp.mapDomain (C i).placeMap (Finsupp.single (g • P) (D P) - Finsupp.single P (D P)) =
        Finsupp.mapDomain (C i).placeMap (Finsupp.single (g • P) (D P)) -
          Finsupp.mapDomain (C i).placeMap (Finsupp.single P (D P)) :=
      map_sub (Finsupp.mapDomain.addMonoidHom (C i).placeMap) _ _
    rw [this, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hgpl i P hP.2, sub_self]

  let sA := s.filter (fun P => ¬ isC P)
  have eOf : ∀ j : sA, ∃ e, (j : Place L F) ∈ (An e).dom ∧ ∃ (v : Aˣ) (jj : ℕ),
      ((j : Place L F).evalAt (An e).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L) ^ jj := fun j => hann j j.2
  let e : sA → Fin m := fun j => (eOf j).choose
  have he : ∀ j : sA, (j : Place L F) ∈ (An (e j)).dom ∧ ∃ (v : Aˣ) (jj : ℕ),
      ((j : Place L F).evalAt (An (e j)).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L) ^ jj :=
    fun j => (eOf j).choose_spec
  let nq : sA → ℤ := fun j => D j
  let Q : sA → Fin 4 → Place L F := fun j l => if l = 0 then g • (j : Place L F) else (j : Place L F)
  have hQ0 : ∀ j, Q j 0 = g • (j : Place L F) := fun j => if_pos rfl
  have hQ1 : ∀ j, Q j 1 = (j : Place L F) := fun j => if_neg (by decide)
  have hQ2 : ∀ j, Q j 2 = (j : Place L F) := fun j => if_neg (by decide)
  have hQ3 : ∀ j, Q j 3 = (j : Place L F) := fun j => if_neg (by decide)
  have hQ : ∀ j l, Q j l ∈ (An (e j)).dom := by
    intro j l
    by_cases hl : l = 0
    · subst hl; rw [hQ0]; exact hgAn (e j) _ (he j).1
    · show (if l = 0 then g • (j : Place L F) else (j : Place L F)) ∈ (An (e j)).dom
      rw [if_neg hl]; exact (he j).1

  have hshift : ∀ j : sA, (g • (j : Place L F)).evalAt (An (e j)).param =
      SemilinearAut.baseAut g ((j : Place L F).evalAt (An (e j)).param) :=
    fun j => ann_evalAt_smul (An (e j)) (An (e j)).param g (hgAn (e j)) (hgpar (e j)) j (he j).1
  have hrad : ∀ j, ∃ u : Aˣ,
      (Q j 0).evalAt (An (e j)).param = ((u : A) : L) * (Q j 2).evalAt (An (e j)).param := by
    intro j
    rw [hQ0, hQ2, hshift]
    have hne : (j : Place L F).evalAt (An (e j)).param ≠ 0 := ((An (e j)).mem_dom _ (he j).1).2.2.2.1
    exact ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne A π hπ hπ0 hrk
      (SemilinearAut.baseAut g) hgA hgπ _ hne
  have hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Q j 0).evalAt (An (e j)).param * (Q j 1).evalAt (An (e j)).param =
        (Q j 2).evalAt (An (e j)).param * (Q j 3).evalAt (An (e j)).param * (1 + ((t : A) : L)) := by
    intro j
    obtain ⟨v, jj, hv⟩ := (he j).2
    have hπL : ((π : A) : L) ≠ 0 := fun h0 => hπ0 (Subtype.ext h0)
    obtain ⟨t, ht, hσ⟩ :=
      ValuationSubring.exists_apply_eq_mul_one_add_of_pow_eq_mul_pow_of_forall_apply_eq_self A ℓ k (π : L) hπL
        (SemilinearAut.baseAut g) hgA hgres hfix _ (v : A) (Units.isUnit v) jj hv
    refine ⟨t, ht, ?_⟩
    rw [hQ0, hQ1, hQ2, hQ3, hshift, hσ]
    ring

  have hN : ((ℓ ^ k : ℕ) : ℤ) • (g • D - D) ∈ Divisor.principal (K := L) (F := F) := by
    rw [smul_sub, smul_comm]
    exact sub_mem (SemilinearAut.smul_mem_principal g hND) hND

  have hsum : (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) = g • D - D := by
    have hquad : ∀ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1) = δ j := by
      intro j
      rw [hQ0, hQ1, hQ2, hQ3]
      show D j • (Finsupp.single (g • (j : Place L F)) (1 : ℤ) + Finsupp.single (j : Place L F) 1
          - Finsupp.single (j : Place L F) 1 - Finsupp.single (j : Place L F) 1) =
        Finsupp.single (g • (j : Place L F)) (D j) - Finsupp.single (j : Place L F) (D j)
      rw [add_sub_cancel_right, smul_sub, Finsupp.smul_single_one, Finsupp.smul_single_one]
    have hA : ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1) = ∑ P ∈ sA, δ P := by
      rw [Finset.sum_congr rfl (fun j _ => hquad j)]
      exact Finset.sum_coe_sort sA δ
    have hCsum : ∑ i, Gi i = ∑ P ∈ s.filter (fun P => isC P), δ P := by
      show ∑ i, ∑ P ∈ s.filter (fun P => P ∈ (C i).dom), δ P = ∑ P ∈ s.filter (fun P => isC P), δ P
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      by_cases hPc : isC P
      · obtain ⟨i0, hi0⟩ := hPc
        have huniq : ∀ j, P ∈ (C j).dom → j = i0 := by
          rcases hcover P with ⟨i1, hi1, hu, -⟩ | ⟨e1, -, -, hno⟩
          · intro j hj; rw [hu j hj, hu i0 hi0]
          · exact absurd hi0 (hno i0)
        rw [if_pos ⟨i0, hi0⟩, Finset.sum_eq_single i0]
        · rw [if_pos hi0]
        · intro j _ hj
          rw [if_neg]
          intro hPj; exact hj (huniq j hPj)
        · intro h; exact absurd (Finset.mem_univ i0) h
      · rw [if_neg hPc]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [if_neg]
        intro hPj; exact hPc ⟨j, hPj⟩
    rw [hA, hCsum, Finset.sum_filter_add_sum_filter_not, hδ]
  have key := htf Gi hGi hred sA e nq Q hQ hrad hbal (by rw [hsum]; exact hN)
  rw [hsum] at key
  exact key

end KLB

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
    (g : SemilinearAut L F)
    (hg : (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A) ∧ SemilinearAut.baseAut g (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut g (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut g (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, g • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, g • P ∈ (An e).dom) ∧
      (∀ e, g • (An e).param = (An e).param) ∧ (∀ e, g • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : g • f ∈ (C i).integers,
        (C i).residue ⟨g • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = (C i).placeMap P))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (k : ℕ) (hfix : ∀ r : L, r ^ (ℓ ^ k) = (π : L) → SemilinearAut.baseAut g r = r)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ c : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • c = 0 → g • c = c := by
  classical
  obtain ⟨hgA, hgπ, hgres, hgC, hgAn, hgpar, -, -, hgpl⟩ := hg
  refine KLB.core A π hπ hπ0 hrk F n m Fbar C An hcover g hgA hgπ hgres hgC hgAn hgpar hgpl ℓ k hfix ?_ ?_
  · exact AlgebraicCurve.exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus ℓ k M D
  · intro Gi hGi hred ι _ e nq Q hQ hrad hbal hkG
    have hk : IsUnit (((ℓ ^ k : ℕ) : ℕ) : IsLocalRing.ResidueField A) := by
      rw [Nat.cast_pow]; exact hℓ.pow k
    have hgenus' : genusFF L F + Fintype.card (Fin n) =
        (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card (Fin m) + 1 := by
      simpa only [Fintype.card_fin] using hgenus
    exact AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus'
      M D (ℓ ^ k) hk Gi hGi hred e nq Q hQ hrad hbal hkG

end S_AlgebraicCurve_smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel (solution)
