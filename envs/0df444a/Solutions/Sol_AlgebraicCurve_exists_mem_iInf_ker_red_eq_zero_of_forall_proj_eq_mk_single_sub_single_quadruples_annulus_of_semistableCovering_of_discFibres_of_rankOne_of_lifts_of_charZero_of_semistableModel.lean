-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5ea0d299-5f54-5829-8ebe-5d835e2c0770

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
import Theorems.Thm_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt
import Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

namespace VCToricA

theorem mem_of_pow_eq_one {L : Type} [Field L] (A : ValuationSubring L) {ζ : L} {N : ℕ} (hN : 0 < N)
    (hζ : ζ ^ N = 1) : ζ ∈ A := by
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have hζ' : ζ ^ (N - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hN, hζ]
    have : ζ = (ζ⁻¹) ^ (N - 1) := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right hζ'
    rw [this]
    exact pow_mem h _

theorem apply_eq_self_of_pow_eq_one {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A)
    (hres : ∀ (a : A) (h : σ (a : L) ∈ A),
      IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a)
    (N : ℕ) (hN : ((N : ℕ) : IsLocalRing.ResidueField A) ≠ 0) (ζ : L) (hζ : ζ ^ N = 1) :
    σ ζ = ζ := by
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simp [h]) hN
    · exact h
  have hζA : ζ ∈ A := mem_of_pow_eq_one A hN0 hζ
  have hσζA : σ ζ ∈ A := (hA ζ).1 hζA
  have h1 : (⟨ζ, hζA⟩ : A) ^ N = 1 := Subtype.ext (by push_cast; exact hζ)
  have h2 : (⟨σ ζ, hσζA⟩ : A) ^ N = 1 := Subtype.ext (by push_cast; rw [← map_pow, hζ, map_one])
  have key := (ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed L A N hN).1
    ⟨σ ζ, hσζA⟩ ⟨ζ, hζA⟩ h2 h1 (hres ⟨ζ, hζA⟩ hσζA)
  exact congrArg Subtype.val key

theorem exists_unit_eq_apply {L : Type} [Field L] (A : ValuationSubring L)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A) (u : Aˣ) :
    ∃ u' : Aˣ, ((u' : A) : L) = σ ((u : A) : L) := by
  have hu : σ ((u : A) : L) ∈ A := (hA _).1 (u : A).2
  have hui : σ ((u⁻¹ : Aˣ) : A) ∈ A := (hA _).1 ((u⁻¹ : Aˣ) : A).2
  refine ⟨⟨⟨_, hu⟩, ⟨_, hui⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · push_cast
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  · push_cast
    rw [← map_mul, ← Subring.coe_mul, Units.inv_mul]; simp

theorem xi_pow_eq_one {L : Type} [Field L] {ℓ : ℕ} (ξ : ℕ → L) (hξ0 : ξ 0 = 1)
    (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (k : ℕ) : ξ k ^ ℓ ^ k = 1 := by
  induction k with
  | zero => simpa using hξ0
  | succ k ih => rw [pow_succ', pow_mul, hξ k, ih]

end VCToricA

namespace VCToricA

theorem mk_eq_mk_iff {K F : Type} [Field K] [Field F] [Algebra K F]
    (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ ((D : Divisor K F) - E) ∈ Divisor.principal (K := K) (F := F) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem mk_sub' {K F : Type} [Field K] [Field F] [Algebra K F]
    (D E : Divisor.degZero (K := K) (F := F)) : Pic0.mk (D - E) = Pic0.mk D - Pic0.mk E := rfl

theorem mk_zsmul' {K F : Type} [Field K] [Field F] [Algebra K F]
    (m : ℤ) (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk (m • D) = m • Pic0.mk D := rfl

theorem mk_eq_zero_iff {K F : Type} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ (D : Divisor K F) ∈ Divisor.principal (K := K) (F := F) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem degree_eq_sum {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (D : Divisor K F) : Divisor.degree D = D.sum (fun _ n => n) := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro v _
  simp [IsCurveOver.deg_eq_one_of_isAlgClosed v]

theorem degree_eq_zero_of_mapDomain_eq_zero {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] {β : Type} (f : Place K F → β) (D : Divisor K F) (h : Finsupp.mapDomain f D = 0) :
    Divisor.degree D = 0 := by
  rw [degree_eq_sum]
  have := congrArg (fun E : β →₀ ℤ => E.sum (fun _ n => n)) h
  simp only [Finsupp.sum_zero_index] at this
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)] at this
  exact this

theorem degree_single_eq_one {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (P : Place K F) : Divisor.degree (Finsupp.single P 1) = 1 := by
  rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed P]; simp

theorem mem_dom_of_mem_support_smul {K F : Type} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (S : Set (Place K F)) (hS : ∀ P ∈ S, g • P ∈ S)
    (D : Divisor K F) (hD : ∀ P ∈ D.support, P ∈ S) : ∀ P ∈ (g • D).support, P ∈ S := by
  intro P hP
  rw [Finsupp.mem_support_iff, SemilinearAut.divisor_smul_apply] at hP
  have h := hS _ (hD _ (Finsupp.mem_support_iff.mpr hP))
  rwa [smul_inv_smul] at h

theorem mapDomain_smul_eq {K F : Type} [Field K] [Field F] [Algebra K F] {β : Type}
    (g : SemilinearAut K F) (S : Set (Place K F)) (f : Place K F → β)
    (hf : ∀ P ∈ S, f (g • P) = f P) (D : Divisor K F) (hD : ∀ P ∈ D.support, P ∈ S) :
    Finsupp.mapDomain f (g • D) = Finsupp.mapDomain f D := by
  rw [SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp]
  unfold Finsupp.mapDomain
  apply Finsupp.sum_congr
  intro P hP
  simp only [Function.comp_apply, hf P (hD P hP)]

theorem deg_eq_one_of_isRational {K F : Type} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) := ⟨v.algebraMap_residueField_injective, hv⟩
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

theorem degree_eq_sum_of_forall_isRational {K F : Type} [Field K] [Field F] [Algebra K F]
    (hrat : ∀ v : Place K F, v.IsRational) (D : Divisor K F) : Divisor.degree D = D.sum (fun _ n => n) := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro v _
  simp [deg_eq_one_of_isRational v (hrat v)]

theorem smul_proj_eq
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (π : A)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    {n : ℕ} {Fbar : Fin n → Type} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))
    {m : ℕ} (An : Fin m → Annulus A F) (e : Fin m) (hmod0 : (((An e).modulus : A) : L) ≠ 0) (w : ℕ)
    (hw : ∃ u : Aˣ, (An e).modulus = u * π ^ w)
    (s : SemilinearAut L F)
    (hA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A)
    (hσπ : SemilinearAut.baseAut s (π : L) = (π : L))
    (hres : ∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
      IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a)
    (hCdom : ∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom)
    (hAdom : ∀ e', ∀ P ∈ (An e').dom, s • P ∈ (An e').dom)
    (hpar : ∀ e', s • (An e').param = (An e').param)
    (hpm : ∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k)
    (y : TateModule ℓ (Pic0 L F))
    (hy : ∀ (k : ℕ) (Q Q' : Place L F), Q ∈ (An e).dom → Q' ∈ (An e).dom →
        (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (Q.evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d) →
        Q'.evalAt (An e).param = ξ k * Q.evalAt (An e).param →
        ∃ (Di : Fin n → Divisor L F) (r : ℕ) (eq : Fin r → Fin m) (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F),
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
          (∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0) ∧
          (∀ j l, Qq j l ∈ (An (eq j)).dom) ∧
          (∀ j, (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 0).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d) ∧
            (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 1).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d)) ∧
          (∀ j, ∃ u : Aˣ,
            (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) ∧
          (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
            (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
              (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) ∧
          ∀ hD : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) ∈
              Divisor.degZero (K := L) (F := F),
            TateModule.proj ℓ (Pic0 L F) k y = Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F), hD⟩)
    (k : ℕ)
    (hKT : ∀ (G : Fin n → Divisor L F) {ι : Type} [Fintype ι] (eq : ι → Fin m) (nq : ι → ℤ) (Qq : ι → Fin 4 → Place L F),
        (∀ i, ∀ P ∈ (G i).support, P ∈ (C i).dom) →
        (∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0) →
        (∀ j l, Qq j l ∈ (An (eq j)).dom) →
        (∀ j, ∃ u : Aˣ, (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) →
        (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
          (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
            (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) →
        ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈
          Divisor.principal (K := L) (F := F) →
        (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈ Divisor.principal (K := L) (F := F)) :
    s • (y : ℕ → Pic0 L F) k = (y : ℕ → Pic0 L F) k := by
  classical
  set σ := SemilinearAut.baseAut s with hσ
  have hℓk : ((ℓ ^ k : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Nat.cast_pow]; exact (hℓ.pow k).ne_zero
  have hξk : ξ k ^ ℓ ^ k = 1 := xi_pow_eq_one ξ hξ0 hξ k
  have hσξ : σ (ξ k) = ξ k := apply_eq_self_of_pow_eq_one A σ hA hres (ℓ ^ k) hℓk (ξ k) hξk
  have hξA : ξ k ∈ A := mem_of_pow_eq_one A (pow_pos (Fact.out : ℓ.Prime).pos k) hξk
  have hξ0' : ξ k ≠ 0 := by
    intro h; rw [h, zero_pow (pow_pos (Fact.out : ℓ.Prime).pos k).ne'] at hξk; exact zero_ne_one hξk
  have hξinvA : (ξ k)⁻¹ ∈ A := by
    have : (ξ k)⁻¹ ^ ℓ ^ k = 1 := by rw [inv_pow, hξk, inv_one]
    exact mem_of_pow_eq_one A (pow_pos (Fact.out : ℓ.Prime).pos k) this
  have hσm : ∀ t : A, t ∈ IsLocalRing.maximalIdeal A → ∀ h : σ (t : L) ∈ A,
      (⟨σ (t : L), h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro t ht h
    rw [← IsLocalRing.residue_eq_zero_iff] at ht ⊢
    rw [hres t h, ht]

  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (((An e).modulus : A) : L) two_pos
  have hc0 : c ≠ 0 := by rintro rfl; exact hmod0 (by rw [← hc]; simp)
  have hcA : c ∈ A := by
    rcases A.mem_or_inv_mem c with h | h
    · exact h
    · have : c = (((An e).modulus : A) : L) * c⁻¹ := by
        rw [← hc]; field_simp
      rw [this]; exact mul_mem ((An e).modulus).2 h
  have hcm : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem 2
    have : (⟨c, hcA⟩ : A) ^ 2 = (An e).modulus := Subtype.ext (by push_cast; exact hc)
    rw [this]; exact (An e).modulus_mem
  obtain ⟨u, hu⟩ := hw
  have hmodL : (((An e).modulus : A) : L) = ((u : A) : L) * (π : L) ^ w := by
    rw [hu]; push_cast; rfl
  obtain ⟨Q, ⟨hQdom, hQval⟩, -⟩ := (An e).existsUnique_evalAt_eq ⟨c, hcA⟩ hcm (by exact hc0)
    ⟨⟨c, hcA⟩, hcm, by push_cast; rw [← hc, pow_two]⟩
  have hc'A : ξ k * c ∈ A := mul_mem hξA hcA
  have hc'm : (⟨ξ k * c, hc'A⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (⟨ξ k * c, hc'A⟩ : A) = ⟨ξ k, hξA⟩ * ⟨c, hcA⟩ := rfl
    rw [this]; exact Ideal.mul_mem_left _ _ hcm
  obtain ⟨Q', ⟨hQ'dom, hQ'val⟩, -⟩ := (An e).existsUnique_evalAt_eq ⟨ξ k * c, hc'A⟩ hc'm
    (by push_cast; exact mul_ne_zero hξ0' hc0)
    ⟨⟨(ξ k)⁻¹ * c, mul_mem hξinvA hcA⟩, by
      have : (⟨(ξ k)⁻¹ * c, mul_mem hξinvA hcA⟩ : A) = ⟨(ξ k)⁻¹, hξinvA⟩ * ⟨c, hcA⟩ := rfl
      rw [this]; exact Ideal.mul_mem_left _ _ hcm, by
      push_cast; rw [← hc]; field_simp⟩
  obtain ⟨Di, r, eq, nq, Qq, hDidom, hDipush, hQqdom, hQqdepth, hQqrad, hQqbal, hDi⟩ := hy k Q Q' hQdom hQ'dom
    ⟨2, w, u, two_pos, by rw [hQval]; push_cast; rw [hc, hmodL]⟩ (by rw [hQval, hQ'val])

  have hrat : ∀ e', ∀ P ∈ (An e').dom, P.IsRational := fun e' P hP => ((An e').mem_dom P hP).1
  have hval_s : ∀ e', ∀ P ∈ (An e').dom, (s • P).evalAt (An e').param = σ (P.evalAt (An e').param) := by
    intro e' P hP
    have := Place.evalAt_smul_smul_eq_baseAut_evalAt s P (hrat e' P hP) (hrat e' _ (hAdom e' P hP)) (An e').param
    rwa [hpar e'] at this
  have hdepth_s : ∀ e', ∀ P ∈ (An e').dom,
      (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (P.evalAt (An e').param) ^ N = ((u : A) : L) * (π : L) ^ d) →
      ∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((s • P).evalAt (An e').param) ^ N = ((u : A) : L) * (π : L) ^ d := by
    intro e' P hP ⟨N, d, v, hN, hv⟩
    obtain ⟨v', hv'⟩ := exists_unit_eq_apply A σ hA v
    exact ⟨N, d, v', hN, by rw [hval_s e' P hP, ← map_pow, hv, map_mul, map_pow, ← hv', hσπ]⟩
  obtain ⟨u', hu'⟩ := exists_unit_eq_apply A σ hA u
  obtain ⟨Di', r', eq', nq', Qq', hDi'dom, hDi'push, hQq'dom, hQq'depth, hQq'rad, hQq'bal, hDi'⟩ :=
    hy k (s • Q) (s • Q') (hAdom e Q hQdom) (hAdom e Q' hQ'dom)
    ⟨2, w, u', two_pos, by
      rw [hval_s e Q hQdom, ← map_pow, hQval]
      push_cast
      rw [hc, hmodL, map_mul, map_pow, ← hu', hσπ]⟩
    (by rw [hval_s e Q hQdom, hval_s e Q' hQ'dom, hQ'val, hQval]; push_cast; rw [map_mul, hσξ])

  set sQq : Fin r → Fin 4 → Place L F := fun j l => s • Qq j l with hsQq
  have hsQqdom : ∀ j l, sQq j l ∈ (An (eq j)).dom := fun j l => hAdom _ _ (hQqdom j l)
  have hsQqrad : ∀ j, ∃ v : Aˣ, (sQq j 0).evalAt (An (eq j)).param = ((v : A) : L) * (sQq j 2).evalAt (An (eq j)).param := by
    intro j
    obtain ⟨v, hv⟩ := hQqrad j
    obtain ⟨v', hv'⟩ := exists_unit_eq_apply A σ hA v
    refine ⟨v', ?_⟩
    simp only [hsQq]
    rw [hval_s _ _ (hQqdom j 0), hval_s _ _ (hQqdom j 2), hv, map_mul, hv']
  have hsQqbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (sQq j 0).evalAt (An (eq j)).param * (sQq j 1).evalAt (An (eq j)).param =
        (sQq j 2).evalAt (An (eq j)).param * (sQq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L)) := by
    intro j
    obtain ⟨t, ht, htv⟩ := hQqbal j
    have hσt : σ (t : L) ∈ A := (hA _).1 t.2
    refine ⟨⟨σ (t : L), hσt⟩, hσm t ht hσt, ?_⟩
    simp only [hsQq]
    rw [hval_s _ _ (hQqdom j 0), hval_s _ _ (hQqdom j 1), hval_s _ _ (hQqdom j 2), hval_s _ _ (hQqdom j 3),
      ← map_mul, htv, map_mul, map_mul, map_add, map_one]

  have hdegq : ∀ (a b c' d : Place L F), Divisor.degree (Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single c' 1 - Finsupp.single d 1 : Divisor L F) = 0 := by
    intro a b c' d
    rw [map_sub, map_sub, map_add, degree_single_eq_one, degree_single_eq_one,
      degree_single_eq_one, degree_single_eq_one]; ring
  have hdegD : ∀ (G : Fin n → Divisor L F), (∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0) →
      ∀ {r : ℕ} (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F) (P P' : Place L F),
      (Finsupp.single P 1 - Finsupp.single P' 1 - ∑ i, G i -
        ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) ∈ Divisor.degZero (K := L) (F := F) := by
    intro G hG r nq Qq P P'
    rw [Divisor.mem_degZero, map_sub, map_sub, map_sub, map_sum, map_sum, degree_single_eq_one, degree_single_eq_one,
      Finset.sum_eq_zero (fun i _ => degree_eq_zero_of_mapDomain_eq_zero _ _ (hG i)),
      Finset.sum_eq_zero (fun j _ => by rw [map_zsmul, hdegq, smul_zero])]
    simp
  have e1 := hDi (hdegD Di hDipush nq Qq Q Q')
  have e2 := hDi' (hdegD Di' hDi'push nq' Qq' (s • Q) (s • Q'))
  have hsquad : ∀ j, s • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) =
      (Finsupp.single (sQq j 0) 1 + Finsupp.single (sQq j 1) 1 - Finsupp.single (sQq j 2) 1 - Finsupp.single (sQq j 3) 1 : Divisor L F) := by
    intro j
    simp only [hsQq, smul_sub, smul_add, SemilinearAut.smul_single]
  have hsD1 : s • (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i -
      ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) =
      Finsupp.single (s • Q) 1 - Finsupp.single (s • Q') 1 - ∑ i, s • Di i -
      ∑ j, nq j • (Finsupp.single (sQq j 0) 1 + Finsupp.single (sQq j 1) 1 - Finsupp.single (sQq j 2) 1 - Finsupp.single (sQq j 3) 1 : Divisor L F) := by
    rw [smul_sub, smul_sub, smul_sub, Finset.smul_sum, Finset.smul_sum, SemilinearAut.smul_single, SemilinearAut.smul_single]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, hsquad]

  set G : Fin n → Divisor L F := fun i => s • Di i - Di' i with hG
  have hGdom : ∀ i, ∀ P ∈ (G i).support, P ∈ (C i).dom := by
    intro i P hP
    have hP' : P ∈ (s • Di i).support ∪ (Di' i).support := by
      apply Finsupp.support_sub hP
    rcases Finset.mem_union.mp hP' with h | h
    · exact mem_dom_of_mem_support_smul s (C i).dom (hCdom i) (Di i) (hDidom i) P h
    · exact hDi'dom i P h
  have hGpush : ∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0 := by
    intro i
    simp only [hG, Finsupp.mapDomain_sub, hDi'push i,
      mapDomain_smul_eq s (C i).dom (C i).placeMap (hpm i) (Di i) (hDidom i), hDipush i, sub_zero]
  set EQ : Fin r ⊕ Fin r' → Fin m := Sum.elim eq eq' with hEQ
  set NQ : Fin r ⊕ Fin r' → ℤ := Sum.elim nq (fun j => -nq' j) with hNQ
  set QQ : Fin r ⊕ Fin r' → Fin 4 → Place L F := Sum.elim sQq Qq' with hQQ
  have hQQdom : ∀ j l, QQ j l ∈ (An (EQ j)).dom := by
    rintro (j | j) l
    · exact hsQqdom j l
    · exact hQq'dom j l
  have hQQrad : ∀ j, ∃ v : Aˣ, (QQ j 0).evalAt (An (EQ j)).param = ((v : A) : L) * (QQ j 2).evalAt (An (EQ j)).param := by
    rintro (j | j)
    · exact hsQqrad j
    · exact hQq'rad j
  have hQQbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A, (QQ j 0).evalAt (An (EQ j)).param * (QQ j 1).evalAt (An (EQ j)).param =
      (QQ j 2).evalAt (An (EQ j)).param * (QQ j 3).evalAt (An (EQ j)).param * (1 + ((t : A) : L)) := by
    rintro (j | j)
    · exact hsQqbal j
    · exact hQq'bal j
  have hdiff : (Finsupp.single (s • Q) 1 - Finsupp.single (s • Q') 1 - ∑ i, Di' i -
        ∑ j, nq' j • (Finsupp.single (Qq' j 0) 1 + Finsupp.single (Qq' j 1) 1 - Finsupp.single (Qq' j 2) 1 - Finsupp.single (Qq' j 3) 1 : Divisor L F) : Divisor L F) -
      s • (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i -
        ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) =
      ∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F) := by
    rw [hsD1, hG, hNQ, hQQ, Finset.sum_sub_distrib, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
    abel
  set X₁ : Divisor.degZero (K := L) (F := F) :=
    SemilinearAut.degZeroSMulHom s ⟨_, hdegD Di hDipush nq Qq Q Q'⟩ with hX₁
  set X₂ : Divisor.degZero (K := L) (F := F) := ⟨_, hdegD Di' hDi'push nq' Qq' (s • Q) (s • Q')⟩ with hX₂
  have hy1 : s • (y : ℕ → Pic0 L F) k = Pic0.mk X₁ := by
    show s • TateModule.proj ℓ (Pic0 L F) k y = _
    rw [e1, SemilinearAut.pic0_smul_mk]
  have hy2 : (y : ℕ → Pic0 L F) k = Pic0.mk X₂ := e2
  have hX : ((X₂ : Divisor L F) - X₁) = ∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F) := by
    rw [hX₂, hX₁, SemilinearAut.coe_degZeroSMulHom]; exact hdiff
  have htor : ((ℓ ^ k : ℕ) : ℤ) • (Pic0.mk X₂ - Pic0.mk X₁) = 0 := by
    have h1 : ((ℓ ^ k : ℕ) : ℤ) • (y : ℕ → Pic0 L F) k = 0 := TateModule.torsion y k
    have h2 : ((ℓ ^ k : ℕ) : ℤ) • (s • (y : ℕ → Pic0 L F) k) = 0 := by
      rw [← SemilinearAut.smul_zsmul, h1]; exact smul_zero (A := Pic0 L F) s
    rw [← hy1, ← hy2, zsmul_sub, h1, h2, sub_zero]
  have hprin : ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F)) ∈
      Divisor.principal (K := L) (F := F) := by
    rw [← mk_sub', ← mk_zsmul', mk_eq_zero_iff] at htor
    have hc : (((((ℓ ^ k : ℕ) : ℤ) • (X₂ - X₁)) : Divisor.degZero (K := L) (F := F)) : Divisor L F) =
        ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, NQ j • (Finsupp.single (QQ j 0) 1 + Finsupp.single (QQ j 1) 1 - Finsupp.single (QQ j 2) 1 - Finsupp.single (QQ j 3) 1 : Divisor L F)) := by
      rw [← hX]; push_cast; rfl
    rwa [hc] at htor
  have hGprin := hKT G EQ NQ QQ hGdom hGpush hQQdom hQQrad hQQbal hprin
  rw [hy1, hy2, eq_comm, mk_eq_mk_iff, hX]
  exact hGprin

end VCToricA

namespace VCToricA

theorem tate_eq_zero_of_forall_proj {p : ℕ} {M : Type} [AddCommGroup M] (y : TateModule p M)
    (h : ∀ k, TateModule.proj p M k y = 0) : y = 0 :=
  Subtype.ext (funext fun k => by simpa using h k)

theorem tate_eq_zero_of_pow_nsmul_eq_zero {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (y : TateModule p M) (r : ℕ) (h : (p ^ r) • y = 0) : y = 0 := by
  apply Subtype.ext
  funext k
  have hk : (y : ℕ → M) k = ((p ^ r : ℕ) : ℤ) • (y : ℕ → M) (k + r) := (TateModule.compat_pow y k r).symm
  have h' : ((p ^ r) • y : TateModule p M) = 0 := h
  have h'' := congrArg (fun z : TateModule p M => (z : ℕ → M) (k + r)) h'
  simp only [AddSubgroupClass.coe_nsmul, Pi.smul_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h''
  rw [hk, natCast_zsmul, h'']
  rfl

theorem tate_eq_zero_of_smul_eq_zero {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (y : TateModule p M) (s : ℤ_[p]) (hs : s ≠ 0) (h : s • y = 0) : y = 0 := by
  have hs' : s = (PadicInt.unitCoeff hs : ℤ_[p]) * (p : ℤ_[p]) ^ s.valuation := PadicInt.unitCoeff_spec hs
  rw [hs', mul_smul, (Units.isUnit _).smul_eq_zero] at h
  apply tate_eq_zero_of_pow_nsmul_eq_zero y s.valuation
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow]
  exact h

theorem one_tmul_injective {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (y y' : TateModule p M)
    (h : ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y : ModularCurve.RationalTateModule p M) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y') :
    y = y' := by
  have h0 : TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1 (y - y') = 0 := by
    rw [TensorProduct.mk_apply, TensorProduct.tmul_sub, h, sub_self]
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p]) (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1)]
    at h0
  obtain ⟨s, hs⟩ := h0
  have := tate_eq_zero_of_smul_eq_zero (y - y') (s : ℤ_[p]) (nonZeroDivisors.coe_ne_zero s) hs
  exact sub_eq_zero.mp this

private theorem _root_.VCToricA.mem_of_pow_mem {L : Type} [Field L] (A : ValuationSubring L) {y : L} {N : ℕ} (hN : 0 < N)
    (hy : y ^ N ∈ A) : y ∈ A := by
  rw [← A.valuation_le_one_iff] at hy ⊢
  rw [map_pow] at hy
  by_contra h
  exact absurd hy (not_le.mpr (one_lt_pow' (not_le.mp h) hN.ne'))

p2m_export "VCToricA" "mem_of_pow_mem"

theorem exists_unit_sq_eq {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (u : Aˣ) :
    ∃ v : Aˣ, ((v : A) : L) ^ 2 = ((u : A) : L) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((u : A) : L) two_pos
  obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq (((u⁻¹ : Aˣ) : A) : L) two_pos
  have hcA : c ∈ A := mem_of_pow_mem A two_pos (by rw [hc]; exact (u : A).2)
  have hc'A : c' ∈ A := mem_of_pow_mem A two_pos (by rw [hc']; exact ((u⁻¹ : Aˣ) : A).2)
  have hcc' : (c * c') ^ 2 = 1 := by
    rw [mul_pow, hc, hc', ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl

  refine ⟨⟨⟨c, hcA⟩, ⟨c' * (c * c'), mul_mem hc'A (mul_mem hcA hc'A)⟩, Subtype.ext ?_, Subtype.ext ?_⟩, hc⟩
  · push_cast; linear_combination hcc'
  · push_cast; linear_combination hcc'

theorem xi_succ_pow {L : Type} [Field L] {ℓ : ℕ} (ξ : ℕ → L)
    (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (j : ℕ) : ξ (j + 1) ^ ℓ ^ j = ξ 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, hξ (j + 1), ih]

theorem degree_eq_zero_of_mem_principal {K F : Type} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {D : Divisor K F} (hD : D ∈ Divisor.principal (K := K) (F := F)) :
    Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := Divisor.mem_principal.mp hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [this]; exact hdeg

theorem degree_eq_zero_of_mapDomain_mem_principal {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] {K' F' : Type} [Field K'] [Field F'] [Algebra K' F'] [HasPrincipalDivisors K' F']
    (hrat : ∀ v : Place K' F', v.IsRational) (f : Place K F → Place K' F') (D : Divisor K F)
    (h : Finsupp.mapDomain f D ∈ Divisor.principal (K := K') (F := F')) : Divisor.degree D = 0 := by
  have h0 := degree_eq_zero_of_mem_principal h
  rw [degree_eq_sum_of_forall_isRational hrat, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)] at h0
  rw [degree_eq_sum]; exact h0

theorem not_mem_chart_of_mem_annulus {ιP ιC ιA : Type} {domC : ιC → Set ιP} {domA : ιA → Set ιP}
    (hcover : ∀ P : ιP, (∃ i, P ∈ domC i ∧ (∀ j, P ∈ domC j → j = i) ∧ ∀ e, P ∉ domA e) ∨
      (∃ e, P ∈ domA e ∧ (∀ e', P ∈ domA e' → e' = e) ∧ ∀ i, P ∉ domC i))
    {P : ιP} {e : ιA} (hP : P ∈ domA e) : ∀ i, P ∉ domC i := by
  rcases hcover P with ⟨i, -, -, h⟩ | ⟨e', -, -, h⟩
  · exact absurd hP (h e)
  · exact h

theorem annulus_eq_of_mem {ιP ιC ιA : Type} {domC : ιC → Set ιP} {domA : ιA → Set ιP}
    (hcover : ∀ P : ιP, (∃ i, P ∈ domC i ∧ (∀ j, P ∈ domC j → j = i) ∧ ∀ e, P ∉ domA e) ∨
      (∃ e, P ∈ domA e ∧ (∀ e', P ∈ domA e' → e' = e) ∧ ∀ i, P ∉ domC i))
    {P : ιP} {e e' : ιA} (hP : P ∈ domA e) (hP' : P ∈ domA e') : e' = e := by
  rcases hcover P with ⟨i, -, -, h⟩ | ⟨e₀, -, h, -⟩
  · exact absurd hP (h e)
  · rw [h e hP, h e' hP']

theorem chart_eq_of_mem {ιP ιC ιA : Type} {domC : ιC → Set ιP} {domA : ιA → Set ιP}
    (hcover : ∀ P : ιP, (∃ i, P ∈ domC i ∧ (∀ j, P ∈ domC j → j = i) ∧ ∀ e, P ∉ domA e) ∨
      (∃ e, P ∈ domA e ∧ (∀ e', P ∈ domA e' → e' = e) ∧ ∀ i, P ∉ domC i))
    {P : ιP} {i j : ιC} (hP : P ∈ domC i) (hP' : P ∈ domC j) : j = i := by
  rcases hcover P with ⟨i₀, -, h, -⟩ | ⟨e, -, -, h⟩
  · rw [h i hP, h j hP']
  · exact absurd hP (h i)

end VCToricA

set_option maxHeartbeats 1600000 in

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
    (red : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)) →ₗ[ℚ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (hξ1 : ξ 1 ≠ 1)
    (x : Fin m → TateModule ℓ (Pic0 L F))
    (hx : ∀ e : Fin m,
      ∀ (k : ℕ) (Q Q' : Place L F), Q ∈ (An e).dom → Q' ∈ (An e).dom →
        (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (Q.evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d) →
        Q'.evalAt (An e).param = ξ k * Q.evalAt (An e).param →
        ∃ (Di : Fin n → Divisor L F) (r : ℕ) (eq : Fin r → Fin m) (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F),
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
          (∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0) ∧
          (∀ j l, Qq j l ∈ (An (eq j)).dom) ∧
          (∀ j, (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 0).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d) ∧
            (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 1).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d)) ∧
          (∀ j, ∃ u : Aˣ,
            (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) ∧
          (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
            (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
              (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) ∧
          ∀ hD : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1) : Divisor L F) ∈
              Divisor.degZero (K := L) (F := F),
            TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1), hD⟩)
    :
    ∀ e : Fin m, ∃ u : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)),
      (u : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e ∧ red u = 0 := by
  classical
  intro e

  have hKT : ∀ (k : ℕ) (G : Fin n → Divisor L F) {ι : Type} [Fintype ι] (eq : ι → Fin m) (nq : ι → ℤ) (Qq : ι → Fin 4 → Place L F),
      (∀ i, ∀ P ∈ (G i).support, P ∈ (C i).dom) →
      (∀ i, Finsupp.mapDomain (C i).placeMap (G i) = 0) →
      (∀ j l, Qq j l ∈ (An (eq j)).dom) →
      (∀ j, ∃ u : Aˣ, (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) →
      (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
        (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
          (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) →
      ((ℓ ^ k : ℕ) : ℤ) • (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈
        Divisor.principal (K := L) (F := F) →
      (∑ i, G i + ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F)) ∈ Divisor.principal (K := L) (F := F) := by
    intro k G ι _ eq nq Qq hGdom hGpush hQdom hrad hbal hkG
    have hk : IsUnit (((ℓ ^ k : ℕ) : ℕ) : IsLocalRing.ResidueField A) := by
      rw [Nat.cast_pow]; exact hℓ.pow k
    exact AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
      A π hπ hπ0 hrk F Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc
      (by simpa [Fintype.card_fin] using hgenus) M D (ℓ ^ k) hk G hGdom hGpush
      eq nq Qq hQdom hrad hbal hkG

  have hfix : ∀ s ∈ S, TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) s (x e) = x e := by
    intro s hs
    obtain ⟨hA, hσπ, hres, hCdom, hAdom, hpar, -, -, hpm⟩ := hS s hs
    apply Subtype.ext
    funext k
    rw [TateModule.rep_apply]
    exact VCToricA.smul_proj_eq A π C An e (hpair e).2.2.1 (w e) (hw e) s hA hσπ hres hCdom hAdom hpar
      hpm ℓ hℓ ξ hξ0 hξ (x e) (hx e) k (fun G ι _ eq nq Qq => hKT k G eq nq Qq)
  have hmem : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈
      ⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    intro s hs
    rw [ModularCurve.rationalGaloisRep_tmul, hfix s hs]
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩

  funext i
  rw [Pi.zero_apply]

  obtain ⟨cL, hcL⟩ := IsAlgClosed.exists_pow_nat_eq ((((An e).modulus : A)) : L) two_pos
  have hcA : cL ∈ A := VCToricA.mem_of_pow_mem A two_pos (by rw [hcL]; exact ((An e).modulus).2)
  set c : A := ⟨cL, hcA⟩ with hcdef
  have hc0 : (c : L) ≠ 0 := by
    intro h; apply (hpair e).2.2.1; rw [← hcL]; change (c : L) ^ 2 = 0; rw [h, zero_pow two_ne_zero]
  have hcm : c ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem 2
    have : c ^ 2 = (An e).modulus := Subtype.ext (by push_cast; exact hcL)
    rw [this]; exact (An e).modulus_mem
  obtain ⟨u, hu⟩ := hw e
  have hcdepth : ((c : A) : L) ^ 2 = ((u : A) : L) * (π : L) ^ w e := by
    change cL ^ 2 = _; rw [hcL, hu]; push_cast; rfl
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos

  have key : ∀ k : ℕ, 0 < k → ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
      red ⟨_, hmem⟩ i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
        TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = 0 := by
    intro k hk
    have hξk : ξ k ^ ℓ ^ k = 1 := VCToricA.xi_pow_eq_one ξ hξ0 hξ k
    have hξA : ξ k ∈ A := VCToricA.mem_of_pow_eq_one A (pow_pos hℓpos k) hξk
    have hξ0' : ξ k ≠ 0 := by
      intro h; rw [h, zero_pow (pow_pos hℓpos k).ne'] at hξk; exact zero_ne_one hξk
    have hξunit : IsUnit (⟨ξ k, hξA⟩ : A) :=
      IsUnit.of_pow_eq_one (n := ℓ ^ k) (Subtype.ext (by push_cast; exact hξk)) (pow_pos hℓpos k).ne'
    have hunitL : ((((hξunit).unit : Aˣ) : A) : L) = ξ k := congrArg Subtype.val hξunit.unit_spec
    have hinvL : ((((hξunit).unit⁻¹ : Aˣ) : A) : L) = (ξ k)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h1 : ((((hξunit).unit⁻¹ : Aˣ) : A) : L) * ((((hξunit).unit : Aˣ) : A) : L) = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel]; rfl
      rwa [hunitL] at h1

    obtain ⟨Q, ⟨hQdom, hQval⟩, -⟩ := (An e).existsUnique_evalAt_eq c hcm hc0 ⟨c, hcm, by rw [← pow_two, hcL]⟩
    set c' : A := ⟨ξ k, hξA⟩ * c with hc'def
    have hc'L : ((c' : A) : L) = ξ k * ((c : A) : L) := by rw [hc'def]; push_cast; rfl
    have hc'0 : ((c' : A) : L) ≠ 0 := by rw [hc'L]; exact mul_ne_zero hξ0' hc0
    have hξinvA : (ξ k)⁻¹ ∈ A := by
      have : (ξ k)⁻¹ ^ ℓ ^ k = 1 := by rw [inv_pow, hξk, inv_one]
      exact VCToricA.mem_of_pow_eq_one A (pow_pos hℓpos k) this
    obtain ⟨Q', ⟨hQ'dom, hQ'val⟩, -⟩ := (An e).existsUnique_evalAt_eq c' (Ideal.mul_mem_left _ _ hcm) hc'0
      ⟨⟨(ξ k)⁻¹, hξinvA⟩ * c, Ideal.mul_mem_left _ _ hcm, by rw [← hcL, hc'L]; push_cast; field_simp; rfl⟩

    obtain ⟨Di, r, eq, nq, Qq, hDidom, hDipush, hQqdom, hQqdepth, hQqrad, hQqbal, hDi⟩ := hx e k Q Q' hQdom hQ'dom
      ⟨2, w e, u, two_pos, by rw [hQval]; exact hcdepth⟩ (by rw [hQval, hQ'val, hc'L])

    obtain ⟨f₀, Df₀, hf₀0, hDf₀, hDf₀an, E₀, hE₀, hE₀dom, hE₀prin⟩ := AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus e Q Q' hQdom hQ'dom
      ⟨(hξunit).unit⁻¹, by rw [hinvL, hQ'val, hc'L, hQval, ← mul_assoc, inv_mul_cancel₀ hξ0', one_mul]⟩
      ⟨2, w e, u, two_pos, by rw [hQval]; exact hcdepth⟩

    have hpairA : ∀ j, ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
        (∀ e', ∀ P ∈ (An e').dom, Df P = (Finsupp.single (Qq j 0) 1 - Finsupp.single (Qq j 2) 1 : Divisor L F) P) ∧
        ∃ E : Fin n → Divisor L F, Df - (Finsupp.single (Qq j 0) 1 - Finsupp.single (Qq j 2) 1) = ∑ i, E i ∧
          (∀ i, ∀ P ∈ (E i).support, P ∈ (C i).dom) ∧
          ∀ i, Finsupp.mapDomain (C i).placeMap (E i) ∈ Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) :=
      fun j => AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus (eq j) (Qq j 0) (Qq j 2) (hQqdom j 0) (hQqdom j 2) (hQqrad j) (hQqdepth j).1
    have hpairB : ∀ j, ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
        (∀ e', ∀ P ∈ (An e').dom, Df P = (Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) P) ∧
        ∃ E : Fin n → Divisor L F, Df - (Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 3) 1) = ∑ i, E i ∧
          (∀ i, ∀ P ∈ (E i).support, P ∈ (C i).dom) ∧
          ∀ i, Finsupp.mapDomain (C i).placeMap (E i) ∈ Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) := by
      intro j
      obtain ⟨v, hv⟩ := hQqrad j
      obtain ⟨t, ht, htv⟩ := hQqbal j
      have h1t : IsUnit (1 + t : A) := by
        have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-t) (by simpa using ht)
        simpa using this

      have hz0 : (Qq j 0).evalAt (An (eq j)).param ≠ 0 := ((An (eq j)).mem_dom _ (hQqdom j 0)).2.2.2.1
      refine AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus (eq j) (Qq j 1) (Qq j 3) (hQqdom j 1) (hQqdom j 3) ⟨v⁻¹ * h1t.unit, ?_⟩ (hQqdepth j).2
      have hvL : (((v : A) : L)) * (((v⁻¹ : Aˣ) : A) : L) = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
      apply mul_left_cancel₀ hz0
      rw [htv, hv]; push_cast; rw [h1t.unit_spec]; push_cast
      linear_combination (-((Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L)))) * hvL
    choose fA DfA hfA0 hDfA hDfAan EA hEA hEAdom hEAprin using hpairA
    choose fB DfB hfB0 hDfB hDfBan EB hEB hEBdom hEBprin using hpairB

    set Fi : Fin n → Divisor L F := fun i' => -(E₀ i' + Di i') + ∑ j, nq j • (EA j i' + EB j i') with hFi
    have hFidom : ∀ i', ∀ P ∈ (Fi i').support, P ∈ (C i').dom := by
      intro i' P hP
      rw [hFi] at hP
      rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
      · rw [Finsupp.support_neg] at h
        rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
        · exact hE₀dom i' P h'
        · exact hDidom i' P h'
      · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
        have hj' := Finsupp.support_smul hj
        rcases Finset.mem_union.mp (Finsupp.support_add hj') with h' | h'
        · exact hEAdom j i' P h'
        · exact hEBdom j i' P h'
    have hFipush : ∀ i', Finsupp.mapDomain (C i').placeMap (Fi i') ∈
        Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i') := by
      intro i'
      rw [hFi]
      change Finsupp.mapDomain.addMonoidHom (C i').placeMap (-(E₀ i' + Di i') + ∑ j, nq j • (EA j i' + EB j i')) ∈ _
      rw [map_add, map_neg, map_add, map_sum]
      refine add_mem (neg_mem (add_mem (hE₀prin i') ?_)) (AddSubgroup.sum_mem _ fun j _ => ?_)
      · change Finsupp.mapDomain (C i').placeMap (Di i') ∈ _; rw [hDipush i']; exact zero_mem _
      · rw [map_zsmul, map_add]; exact AddSubgroup.zsmul_mem _ (add_mem (hEAprin j i') (hEBprin j i')) _
    have hdegE : ∀ (E : Divisor L F) (i' : Fin n), Finsupp.mapDomain (C i').placeMap E ∈
        Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i') → Divisor.degree E = 0 :=
      fun E i' h => VCToricA.degree_eq_zero_of_mapDomain_mem_principal (hratBar i') _ _ h
    have hFideg : ∀ i', Divisor.degree (Fi i') = 0 := fun i' => hdegE _ i' (hFipush i')
    have hD₀ : (∑ i', Fi i') ∈ Divisor.degZero (K := L) (F := F) := by
      rw [Divisor.mem_degZero, map_sum, Finset.sum_eq_zero (fun i' _ => hFideg i')]
    have hdegq : ∀ (a b c'' d : Place L F), Divisor.degree (Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single c'' 1 - Finsupp.single d 1 : Divisor L F) = 0 := by
      intro a b c'' d
      rw [map_sub, map_sub, map_add, VCToricA.degree_single_eq_one, VCToricA.degree_single_eq_one,
        VCToricA.degree_single_eq_one, VCToricA.degree_single_eq_one]; ring
    have hdegFull : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i', Di i' -
        ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) ∈ Divisor.degZero (K := L) (F := F) := by
      rw [Divisor.mem_degZero, map_sub, map_sub, map_sub, map_sum, map_sum, VCToricA.degree_single_eq_one,
        VCToricA.degree_single_eq_one,
        Finset.sum_eq_zero (fun i' _ => VCToricA.degree_eq_zero_of_mapDomain_eq_zero _ _ (hDipush i')),
        Finset.sum_eq_zero (fun j _ => by rw [map_zsmul, hdegq, smul_zero])]
      simp
    have hprojk : TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨∑ i', Fi i', hD₀⟩ := by
      rw [hDi hdegFull, VCToricA.mk_eq_mk_iff]
      have hpair0 : (Finsupp.single Q 1 - Finsupp.single Q' 1 : Divisor L F) = Df₀ - ∑ i', E₀ i' := by
        rw [← hE₀]; abel
      have hquad : ∀ j, (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) =
          (DfA j - ∑ i', EA j i') + (DfB j - ∑ i', EB j i') := by
        intro j; rw [← hEA j, ← hEB j]; abel
      have hcommA : ∑ i', ∑ j, nq j • EA j i' = ∑ j, ∑ i', nq j • EA j i' := Finset.sum_comm
      have hcommB : ∑ i', ∑ j, nq j • EB j i' = ∑ j, ∑ i', nq j • EB j i' := Finset.sum_comm
      have hident : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i', Di i' -
          ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1 - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 : Divisor L F) : Divisor L F) - ∑ i', Fi i' =
          Df₀ - ∑ j, nq j • (DfA j + DfB j) := by
        simp only [hquad, hFi, hpair0, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib, Finset.smul_sum]
        rw [hcommA, hcommB]
        abel
      rw [hident]
      refine sub_mem (Divisor.mem_principal.mpr ⟨f₀, hf₀0, hDf₀⟩) (AddSubgroup.sum_mem _ fun j _ => ?_)
      exact AddSubgroup.zsmul_mem _ (add_mem (Divisor.mem_principal.mpr ⟨fA j, hfA0 j, hDfA j⟩)
        (Divisor.mem_principal.mpr ⟨fB j, hfB0 j, hDfB j⟩)) _
    obtain ⟨y, hy, hyE⟩ := hred ⟨_, hmem⟩ (x e) rfl k (∑ i', Fi i') hD₀ hprojk.symm Fi rfl hFidom hFideg i
    refine ⟨y, hy, ?_⟩
    have hE₀deg : Finsupp.mapDomain (C i).placeMap (Fi i) ∈
        Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i) :=
      Divisor.mem_degZero.mpr (VCToricA.degree_eq_zero_of_mem_principal (hFipush i))
    rw [hyE ⟨_, hE₀deg⟩ rfl, VCToricA.mk_eq_zero_iff]
    exact hFipush i

  obtain ⟨y1, hy1, hp1⟩ := key 1 one_pos
  rw [hy1]
  suffices hy0 : y1 = 0 by rw [hy0, TensorProduct.tmul_zero]
  apply VCToricA.tate_eq_zero_of_forall_proj
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 := TateModule.torsion y1 0
    rw [pow_zero, Nat.cast_one, one_zsmul] at h0
    rw [TateModule.proj_apply]; exact h0
  · obtain ⟨yk, hyk, hpk⟩ := key k hk
    have : y1 = yk := VCToricA.one_tmul_injective _ _ (hy1 ▸ hyk)
    rw [this]; exact hpk

end S_AlgebraicCurve_exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
