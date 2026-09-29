-- Prove2me | solution 1 for AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ffbf6322-5165-59f3-be9b-acf28225c385

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
import Theorems.Thm_AlgebraicCurve_nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.AlgebraicCurve"
open scoped TensorProduct

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Pic Pic0 genusFF SemilinearAut SemilinearAut.baseAut IsCurveOver SemistableModel nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel"
namespace MonoScale
p2m_open "AlgebraicCurve"

theorem exists_zeta_system {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : L) ≠ 0) :
    ∃ ζ : ℕ → L, (∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) ∧ ∀ k, ζ (k + 1) ^ ℓ = ζ k := by
  classical
  haveI : NeZero (ℓ : L) := ⟨hℓ⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  have hℓp : 0 < ℓ := (Fact.out : ℓ.Prime).pos

  have step : ∀ (k : ℕ) (w : L), IsPrimitiveRoot w (ℓ ^ (k + 1)) →
      ∃ z : L, IsPrimitiveRoot z (ℓ ^ (k + 2)) ∧ z ^ ℓ = w := by
    intro k w hw
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w hℓp
    refine ⟨z, ?_, hz⟩
    have h1 : z ^ ℓ ^ (k + 2) = 1 := by
      rw [show ℓ ^ (k + 2) = ℓ * ℓ ^ (k + 1) by ring, pow_mul, hz, hw.pow_eq_one]
    have h2 : z ^ ℓ ^ (k + 1) ≠ 1 := by
      rw [pow_succ', pow_mul, hz]
      exact hw.pow_ne_one_of_pos_of_lt (pow_pos hℓp k).ne' (Nat.pow_lt_pow_right (Fact.out : ℓ.Prime).one_lt (by omega))
    have h3 : orderOf z = ℓ ^ (k + 2) := orderOf_eq_prime_pow h2 h1
    exact h3 ▸ IsPrimitiveRoot.orderOf z
  choose f hf using step
  let g : (k : ℕ) → {w : L // IsPrimitiveRoot w (ℓ ^ (k + 1))} := fun k =>
    Nat.rec (motive := fun k => {w : L // IsPrimitiveRoot w (ℓ ^ (k + 1))}) ⟨ξ, by simpa using hξ⟩
      (fun k wk => ⟨f k wk.1 wk.2, (hf k wk.1 wk.2).1⟩) k
  refine ⟨fun k => Nat.casesOn k 1 fun k => (g k).1, fun k => ?_, fun k => ?_⟩
  · cases k with
    | zero => simp
    | succ k => exact (g k).2
  · cases k with
    | zero => (have h__af := hξ.pow_eq_one; simp at h__af ⊢; exact h__af)
    | succ k => exact (hf k (g k).1 (g k).2).2

theorem pow_apply_eq_of_forall_apply_eq {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] {k : ℕ}
    {ζ π : L} (hζ : ζ ^ (ℓ ^ k) = 1) (hπ0 : π ≠ 0) (σ : L ≃+* L) {e : ℕ}
    (h : ∀ r : L, r ^ (ℓ ^ k) = π → σ r = ζ ^ e * r) (a : ℕ) :
    ∀ r : L, r ^ (ℓ ^ k) = π → (σ ^ a) r = ζ ^ (a * e) * r := by
  have hk : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k
  obtain ⟨r₀, hr₀⟩ := IsAlgClosed.exists_pow_nat_eq π hk
  have hr₀0 : r₀ ≠ 0 := by
    rintro rfl
    exact hπ0 (by rw [← hr₀, zero_pow hk.ne'])
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hζ
    exact zero_ne_one hζ

  have hσζ : σ ζ = ζ := by
    have h1 := h (ζ * r₀) (by rw [mul_pow, hζ, one_mul, hr₀])
    rw [map_mul, h r₀ hr₀, mul_left_comm] at h1
    exact mul_right_cancel₀ hr₀0 (mul_left_cancel₀ (pow_ne_zero _ hζ0) h1)
  intro r hr
  induction a with
  | zero =>
    rw [pow_zero, zero_mul, pow_zero, one_mul]
    rfl
  | succ a ih =>
    rw [pow_succ']
    show σ ((σ ^ a) r) = _
    rw [ih, map_mul, map_pow, hσζ, h r hr, ← mul_assoc, ← pow_add, Nat.succ_mul]

theorem coe_smul_tmul {ℓ : ℕ} [Fact ℓ.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[ℓ] T]
    (c : ℤ_[ℓ]) (a : ℚ_[ℓ]) (y : T) : (c : ℚ_[ℓ]) • (a ⊗ₜ[ℤ_[ℓ]] y) = a ⊗ₜ[ℤ_[ℓ]] (c • y) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, ← TensorProduct.smul_tmul, Algebra.smul_def]
  rfl

end AlgebraicCurve.MonoScale

end

open AlgebraicCurve.MonoScale in
set_option maxHeartbeats 6400000 in
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
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∃ N : ModularCurve.RationalTateModule ℓ (Pic0 L F) →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (Pic0 L F),
      ∀ s ∈ S, ∃ t : ℤ_[ℓ],
        ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1 = (t : ℚ_[ℓ]) • N ∧
        ((∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r) → IsUnit t) := by
  classical

  have hℓL : (ℓ : L) ≠ 0 := by
    intro h0
    apply hℓ.ne_zero
    have hA : ((ℓ : ℕ) : A) = 0 := by
      apply Subtype.ext
      show ((ℓ : A) : L) = ((0 : A) : L)
      rw [show ((ℓ : A) : L) = A.subtype (ℓ : A) from rfl, map_natCast, h0]
      rfl
    rw [← map_natCast (algebraMap (↥A) (IsLocalRing.ResidueField A)), hA, map_zero]
  obtain ⟨ζ, hζ, hζc⟩ := exists_zeta_system (L := L) ℓ hℓL
  have hπ0' : (π : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)

  have hT : ∀ s ∈ S, ∃ t : ℤ_[ℓ],
      (∀ (k : ℕ) (r : L), r ^ (ℓ ^ k) = (π : L) → SemilinearAut.baseAut s r = ζ k ^ (t.appr k) * r) ∧
      (IsUnit t ↔ ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r) := fun s hs =>
    ValuationSubring.exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq A ℓ hℓ ζ hζ hζc (π : L) hπ0'
      (SemilinearAut.baseAut s) (hS s hs).2.1 (hS s hs).2.2.1
  choose t ht using hT
  obtain ⟨s₀, hs₀, hmv⟩ := hSℓ
  have hu : IsUnit (t s₀ hs₀) := (ht s₀ hs₀).2.mpr hmv
  have hu0 : ((t s₀ hs₀ : ℤ_[ℓ]) : ℚ_[ℓ]) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)

  have key : ∀ (s : ↥(SemilinearAut L F)) (hs : s ∈ S) (x : TateModule ℓ (Pic0 L F)),
      t s₀ hs₀ • (TateModule.rep ℓ (Pic0 L F) ↥(SemilinearAut L F) s x - x) =
        t s hs • (TateModule.rep ℓ (Pic0 L F) ↥(SemilinearAut L F) s₀ x - x) := by
    intro s hs x
    refine Subtype.ext (funext fun k => ?_)
    simp only [TateModule.smul_apply, TateModule.coe_sub, Pi.sub_apply, TateModule.rep_apply]
    have hroots : ∀ r : L, r ^ (ℓ ^ k) = (π : L) →
        ((SemilinearAut.baseAut s) ^ (t s₀ hs₀).appr k) r = ((SemilinearAut.baseAut s₀) ^ (t s hs).appr k) r := by
      intro r hr
      rw [pow_apply_eq_of_forall_apply_eq (hζ k).pow_eq_one hπ0' _ ((ht s hs).1 k) _ r hr,
        pow_apply_eq_of_forall_apply_eq (hζ k).pow_eq_one hπ0' _ ((ht s₀ hs₀).1 k) _ r hr, Nat.mul_comm]
    have hk := AlgebraicCurve.nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus S hS
      hSlift ℓ hℓ ⟨s₀, hs₀, hmv⟩ M D s hs s₀ hs₀ k ((t s₀ hs₀).appr k) ((t s hs).appr k) hroots
      ((x : ℕ → Pic0 L F) k) (TateModule.torsion x k)
    rw [← natCast_zsmul, ← natCast_zsmul] at hk
    exact hk

  set N : ModularCurve.RationalTateModule ℓ (Pic0 L F) →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (Pic0 L F) :=
    ((t s₀ hs₀ : ℤ_[ℓ]) : ℚ_[ℓ])⁻¹ • (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s₀ - 1) with hN
  refine ⟨N, fun s hs => ⟨t s hs, ?_, fun h => (ht s hs).2.mpr h⟩⟩
  have hV : ∀ v : ModularCurve.RationalTateModule ℓ (Pic0 L F),
      ((t s₀ hs₀ : ℤ_[ℓ]) : ℚ_[ℓ]) • (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s v - v) =
        ((t s hs : ℤ_[ℓ]) : ℚ_[ℓ]) • (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s₀ v - v) := by
    intro v
    rw [ModularCurve.rationalGaloisRep_apply, ModularCurve.rationalGaloisRep_apply]
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero, sub_zero, smul_zero]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub, ← TensorProduct.tmul_sub,
        coe_smul_tmul, coe_smul_tmul, key s hs x]
    | add v w hv hw => simp only [map_add, add_sub_add_comm, smul_add, hv, hw]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sub_apply, Module.End.one_apply, hN, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply]
  calc _ = ((t s₀ hs₀ : ℤ_[ℓ]) : ℚ_[ℓ])⁻¹ • (((t s₀ hs₀ : ℤ_[ℓ]) : ℚ_[ℓ]) •
          (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s v - v)) := (inv_smul_smul₀ hu0 _).symm
    _ = _ := by rw [hV v, smul_comm]

end S_AlgebraicCurve_exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
