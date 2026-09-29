-- Prove2me | solution 1 for AlgebraicCurve.red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4d904b8b-9b8d-5358-9e0e-fc4cd3432fb9

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
import Theorems.Thm_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
import Theorems.Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

open AlgebraicCurve

namespace MonodromyDiesEngine

namespace Tate

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

theorem eq_zero_of_prime_smul_eq_zero (x : TateModule p M) (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h1 : (((p : ℤ_[p]) • x : TateModule p M) : ℕ → M) (n + 1) = 0 := by
    rw [h]; rfl
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat] at h1
  rw [h1]; rfl

theorem eq_zero_of_prime_pow_smul_eq_zero (k : ℕ) (x : TateModule p M)
    (h : ((p : ℤ_[p]) ^ k) • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, mul_smul] at h
    exact eq_zero_of_prime_smul_eq_zero x (ih _ h)

scoped instance noZeroSMulDivisors : NoZeroSMulDivisors ℤ_[p] (TateModule p M) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    rw [PadicInt.unitCoeff_spec ha] at h
    have h' : ((p : ℤ_[p]) ^ a.valuation) • x = 0 := by
      have := congrArg (fun y => (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y) h
      beta_reduce at this
      rwa [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact eq_zero_of_prime_pow_smul_eq_zero _ x h'

abbrev toRational : TateModule p M →ₗ[ℤ_[p]] ℚ_[p] ⊗[ℤ_[p]] TateModule p M :=
  TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1

theorem toRational_apply (y : TateModule p M) : toRational y = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y := rfl

scoped instance isLocalizedModule_toRational :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (toRational (p := p) (M := M)) :=
  inferInstance

theorem one_tmul_injective :
    Function.Injective (fun y : TateModule p M => (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y) := by
  intro y y' h
  have h0 : toRational (y - y') = 0 := by
    rw [map_sub, toRational_apply, toRational_apply, sub_eq_zero]; exact h
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p]) (toRational)).mp h0
  rw [Submonoid.smul_def, smul_eq_zero] at hs
  rcases hs with hs | hs
  · exact absurd hs (nonZeroDivisors.coe_ne_zero s)
  · exact sub_eq_zero.mp hs

theorem exists_smul_eq_one_tmul (v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) :
    ∃ (a : ℤ_[p]) (x : TateModule p M), a ≠ 0 ∧ (a : ℚ_[p]) • v = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x := by
  obtain ⟨⟨x, s⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) (toRational) v
  refine ⟨s, x, nonZeroDivisors.coe_ne_zero s, ?_⟩
  rw [Submonoid.smul_def] at h
  rw [show ((s : ℤ_[p]) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) from rfl, algebraMap_smul]
  exact h

theorem coe_smul_one_tmul (a : ℤ_[p]) (y : TateModule p M) :
    ((a : ℚ_[p]) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) =
      (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (a • y) := by
  rw [show ((a : ℤ_[p]) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] a from rfl, algebraMap_smul,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul]

variable {G : Type} [Monoid G] [DistribMulAction G M]

theorem rationalGaloisRep_sub_self_one_tmul (g : G) (x : TateModule p M) :
    ModularCurve.rationalGaloisRep p M G g ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) - (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x =
      (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (TateModule.rep p M G g x - x) := by
  rw [ModularCurve.rationalGaloisRep_tmul, TensorProduct.tmul_sub]

theorem proj_smul (a : ℤ_[p]) (y : TateModule p M) (k : ℕ) :
    TateModule.proj p M k (a • y) = (a.appr k) • TateModule.proj p M k y := by
  rw [TateModule.proj_apply, TateModule.proj_apply, TateModule.smul_apply, natCast_zsmul]

end Tate
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate"

namespace SpanClear

open Tate

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] {G : Type} [Monoid G] [DistribMulAction G M]

theorem exists_clear (S : Set G) (v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M)
    (hv : v ∈ Submodule.span ℚ_[p]
      {u | ∃ s ∈ S, ∃ w, u = ModularCurve.rationalGaloisRep p M G s w - w}) :
    ∃ (a : ℤ_[p]) (y : TateModule p M), a ≠ 0 ∧
      y ∈ Submodule.span ℤ_[p] {t | ∃ s ∈ S, ∃ x, t = TateModule.rep p M G s x - x} ∧
      (a : ℚ_[p]) • v = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y := by
  induction hv using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨s, hs, w, rfl⟩ := hu
    obtain ⟨b, x, hb, hbw⟩ := exists_smul_eq_one_tmul w
    refine ⟨b, TateModule.rep p M G s x - x, hb, Submodule.subset_span ⟨s, hs, x, rfl⟩, ?_⟩
    rw [smul_sub, ← LinearMap.map_smul, hbw, rationalGaloisRep_sub_self_one_tmul]
  | zero => exact ⟨1, 0, one_ne_zero, Submodule.zero_mem _, by simp⟩
  | add u u' _ _ hu hu' =>
    obtain ⟨a, y, ha, hy, hau⟩ := hu
    obtain ⟨a', y', ha', hy', hau'⟩ := hu'
    refine ⟨a * a', a' • y + a • y', mul_ne_zero ha ha',
      Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hy'), ?_⟩
    rw [smul_add, PadicInt.coe_mul, mul_comm (a : ℚ_[p]) (a' : ℚ_[p]), mul_smul, hau, mul_comm,
      mul_smul, hau', coe_smul_one_tmul, coe_smul_one_tmul, TensorProduct.tmul_add]
  | smul c u _ hu =>
    obtain ⟨a, y, ha, hy, hau⟩ := hu
    obtain ⟨⟨d, b⟩, hdb⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) c

    have hb : (b : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    have hdb' : c * ((b : ℤ_[p]) : ℚ_[p]) = (d : ℚ_[p]) := hdb
    refine ⟨a * b, d • y, mul_ne_zero ha hb, Submodule.smul_mem _ _ hy, ?_⟩
    rw [PadicInt.coe_mul, smul_smul, mul_assoc, mul_comm ((b : ℤ_[p]) : ℚ_[p]) c, hdb',
      mul_comm, mul_smul, hau, coe_smul_one_tmul]

end SpanClear
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate"

namespace Null

open IsLocalRing

section general

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem smul_mk_sub_mk (g : SemilinearAut K F) (D : Divisor.degZero (K := K) (F := F)) :
    g • Pic0.mk D - Pic0.mk D = Pic0.mk (SemilinearAut.degZeroSMulHom g D - D) := by
  rw [SemilinearAut.pic0_smul_mk]
  change (QuotientAddGroup.mk (SemilinearAut.degZeroSMulHom g D) : Pic0 K F) -
      QuotientAddGroup.mk D = QuotientAddGroup.mk _
  rw [← QuotientAddGroup.mk_sub]

theorem mapDomain_smul_eq_of_forall {β : Type*} (φ : Place K F → β) (g : SemilinearAut K F)
    (D : Divisor K F) (h : ∀ P ∈ D.support, φ (g • P) = φ P) :
    Finsupp.mapDomain φ (g • D) = Finsupp.mapDomain φ D := by
  rw [SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun P hP => h P hP

theorem mapDomain_sub' {α β : Type*} (φ : α → β) (D E : α →₀ ℤ) :
    Finsupp.mapDomain φ (D - E) = Finsupp.mapDomain φ D - Finsupp.mapDomain φ E :=
  map_sub (Finsupp.mapDomain.addMonoidHom φ) D E

theorem mem_support_smul_iff (g : SemilinearAut K F) (D : Divisor K F) (P : Place K F) :
    P ∈ (g • D).support ↔ g⁻¹ • P ∈ D.support := by
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, SemilinearAut.divisor_smul_apply]

theorem sum_smul (g : SemilinearAut K F) (D : Divisor K F) :
    ((g • D).sum fun _ k => k) = D.sum fun _ k => k := by
  rw [SemilinearAut.divisor_smul_def]
  exact Finsupp.sum_mapDomain_index_inj (MulAction.injective g)

theorem prod_smul {N : Type*} [CommMonoid N] (g : SemilinearAut K F) (D : Divisor K F)
    (b : Place K F → ℤ → N) :
    ((g • D).prod b) = D.prod fun P k => b (g • P) k := by
  rw [SemilinearAut.divisor_smul_def]
  exact Finsupp.prod_mapDomain_index_inj (MulAction.injective g)

open scoped Pointwise in

theorem evalAt_smul_smul (g : SemilinearAut K F) (P : Place K F) (hP : P.IsRational)
    (hgP : (g • P).IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    (g • P).evalAt (g • f) = SemilinearAut.baseAut g (P.evalAt f) := by
  have hgf : g • f ∈ (g • P).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g f _ hf
  apply (g • P).algebraMap_residueField_injective
  rw [(g • P).algebraMap_evalAt hgP hgf, ← SemilinearAut.smulResidueRingEquiv_algebraMap g P,
    P.algebraMap_evalAt hP hf]
  symm
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem evalAt_smul_of_smul_eq (g : SemilinearAut K F) (P : Place K F) (hP : P.IsRational)
    (hgP : (g • P).IsRational) {f : F} (hf : f ∈ P.toValuationSubring) (hgf : g • f = f) :
    (g • P).evalAt f = SemilinearAut.baseAut g (P.evalAt f) := by
  conv_lhs => rw [← hgf]
  exact evalAt_smul_smul g P hP hgP hf

theorem prod_zpow_sub {α G₀ : Type*} [CommGroupWithZero G₀] (b : α → G₀) (D E : α →₀ ℤ)
    (hD : ∀ a ∈ D.support, b a ≠ 0) (hE : ∀ a ∈ E.support, b a ≠ 0) :
    ((D - E).prod fun a k => b a ^ k) = (D.prod fun a k => b a ^ k) * (E.prod fun a k => b a ^ k)⁻¹ := by
  classical
  rw [sub_eq_add_neg, Finsupp.prod_add_index]
  · congr 1
    rw [Finsupp.prod_neg_index (fun a => zpow_zero (b a))]
    simp only [zpow_neg]
    exact Finset.prod_inv_distrib _
  · intro a _
    exact zpow_zero (b a)
  · intro a ha b₁ b₂
    rw [Finsupp.support_neg] at ha
    have hb : b a ≠ 0 := by
      rcases Finset.mem_union.mp ha with h | h
      · exact hD a h
      · exact hE a h
    exact zpow_add₀ hb b₁ b₂

theorem prod_zpow_add {α G₀ : Type*} [CommGroupWithZero G₀] (b : α → G₀) (D E : α →₀ ℤ)
    (hD : ∀ a ∈ D.support, b a ≠ 0) (hE : ∀ a ∈ E.support, b a ≠ 0) :
    ((D + E).prod fun a k => b a ^ k) = (D.prod fun a k => b a ^ k) * (E.prod fun a k => b a ^ k) := by
  classical
  rw [Finsupp.prod_add_index]
  · intro a _
    exact zpow_zero (b a)
  · intro a ha b₁ b₂
    have hb : b a ≠ 0 := by
      rcases Finset.mem_union.mp ha with h | h
      · exact hD a h
      · exact hE a h
    exact zpow_add₀ hb b₁ b₂

theorem prod_zpow_neg {α G₀ : Type*} [CommGroupWithZero G₀] (b : α → G₀) (E : α →₀ ℤ) :
    ((-E).prod fun a k => b a ^ k) = (E.prod fun a k => b a ^ k)⁻¹ := by
  rw [Finsupp.prod_neg_index (fun a => zpow_zero (b a))]
  simp only [zpow_neg]
  exact Finset.prod_inv_distrib _

theorem sum_neg' {α : Type*} (E : α →₀ ℤ) :
    ((-E).sum fun (_ : α) (k : ℤ) => k) = -(E.sum fun (_ : α) (k : ℤ) => k) := by
  rw [Finsupp.sum_neg_index (h := fun (_ : α) (k : ℤ) => k) (fun _ => rfl)]
  simp only [Finsupp.sum, Finset.sum_neg_distrib]

end general
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {n m : ℕ} {Fbar : Fin n → Type*} [∀ i, Field (Fbar i)]
  [∀ i, Algebra (ResidueField A) (Fbar i)]

theorem valuation_evalAt_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    A.valuation (P.evalAt An.param) ≠ 0 := by
  obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
  exact (Valuation.ne_zero_iff _).mpr hne

variable (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)

def IsNull (c : Pic0 L F) : Prop :=
  ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Dc : Fin n → Divisor L F)
    (Ne : Fin m → Divisor L F),
    Pic0.mk ⟨D, hD⟩ = c ∧ D = ∑ i, Dc i + ∑ e, Ne e ∧
    (∀ i, ∀ P ∈ (Dc i).support, P ∈ (C i).dom) ∧ (∀ i, Divisor.degree (Dc i) = 0) ∧
    (∀ i, Finsupp.mapDomain (C i).placeMap (Dc i) = 0) ∧
    (∀ e, ∀ P ∈ (Ne e).support, P ∈ (An e).dom) ∧ (∀ e, ((Ne e).sum fun _ k => k) = 0) ∧
    (∀ e, ((Ne e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) = 1)

variable {C An}

theorem isNull_zero : IsNull C An 0 := by
  refine ⟨0, zero_mem _, 0, 0, rfl, by simp, fun i P hP => by simp at hP, fun i => by simp,
    fun i => by simp, fun e P hP => by simp at hP, fun e => by simp, fun e => by simp⟩

theorem isNull_add {c c' : Pic0 L F} (hc : IsNull C An c) (hc' : IsNull C An c') :
    IsNull C An (c + c') := by
  classical
  obtain ⟨D, hD, Dc, Ne, hmk, hsplit, hDcdom, hDcdeg, hDcmap, hNedom, hNesum, hNeprod⟩ := hc
  obtain ⟨D', hD', Dc', Ne', hmk', hsplit', hDcdom', hDcdeg', hDcmap', hNedom', hNesum', hNeprod'⟩ :=
    hc'
  refine ⟨D + D', add_mem hD hD', fun i => Dc i + Dc' i, fun e => Ne e + Ne' e, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← hmk, ← hmk', ← Pic0.mk_add]; rfl
  · rw [hsplit, hsplit', Finset.sum_add_distrib, Finset.sum_add_distrib]; abel
  · intro i P hP
    rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
    · exact hDcdom i P h
    · exact hDcdom' i P h
  · intro i; rw [map_add, hDcdeg, hDcdeg', add_zero]
  · intro i; rw [Finsupp.mapDomain_add, hDcmap, hDcmap', add_zero]
  · intro e P hP
    rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
    · exact hNedom e P h
    · exact hNedom' e P h
  · intro e
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hNesum, hNesum', add_zero]
  · intro e
    rw [prod_zpow_add _ _ _ (fun P hP => valuation_evalAt_ne_zero (An e) (hNedom e P hP))
      (fun P hP => valuation_evalAt_ne_zero (An e) (hNedom' e P hP)), hNeprod, hNeprod', mul_one]

theorem isNull_nsmul {c : Pic0 L F} (hc : IsNull C An c) (k : ℕ) : IsNull C An (k • c) := by
  induction k with
  | zero => rw [zero_nsmul]; exact isNull_zero
  | succ k ih => rw [succ_nsmul]; exact isNull_add ih hc

variable (hcover : ∀ P : Place L F,
    (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
    (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
variable (s : SemilinearAut L F)
  (hsC : ∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) (hsAn : ∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom)

include hcover in
theorem chart_eq_of_mem_dom {P : Place L F} {i j : Fin n} (hi : P ∈ (C i).dom) (hj : P ∈ (C j).dom) :
    i = j := by
  rcases hcover P with ⟨i₀, -, huq, -⟩ | ⟨e, -, -, hno⟩
  · exact (huq i hi).trans (huq j hj).symm
  · exact absurd hi (hno i)

include hcover in
theorem annulus_eq_of_mem_dom {P : Place L F} {e e' : Fin m} (he : P ∈ (An e).dom)
    (he' : P ∈ (An e').dom) : e = e' := by
  rcases hcover P with ⟨i, -, -, hno⟩ | ⟨e₀, -, huq, -⟩
  · exact absurd he (hno e)
  · exact (huq e he).trans (huq e' he').symm

include hcover in
theorem not_mem_dom_of_mem_annulus {P : Place L F} {i : Fin n} {e : Fin m} (hi : P ∈ (C i).dom)
    (he : P ∈ (An e).dom) : False := by
  rcases hcover P with ⟨i₀, -, -, hno⟩ | ⟨e₀, -, -, hno⟩
  · exact hno e he
  · exact hno i hi

include hcover hsC hsAn in

theorem mem_dom_iff_smul_mem_dom (i : Fin n) (P : Place L F) :
    P ∈ (C i).dom ↔ s • P ∈ (C i).dom := by
  refine ⟨hsC i P, fun h => ?_⟩
  rcases hcover P with ⟨j, hj, -, -⟩ | ⟨e, he, -, -⟩
  · rwa [chart_eq_of_mem_dom hcover h (hsC j P hj)]
  · exact (not_mem_dom_of_mem_annulus hcover h (hsAn e P he)).elim

include hcover hsC hsAn in

theorem mem_annulus_iff_smul_mem_annulus (e : Fin m) (P : Place L F) :
    P ∈ (An e).dom ↔ s • P ∈ (An e).dom := by
  refine ⟨hsAn e P, fun h => ?_⟩
  rcases hcover P with ⟨j, hj, -, -⟩ | ⟨e', he', -, -⟩
  · exact (not_mem_dom_of_mem_annulus hcover (hsC j P hj) h).elim
  · rwa [annulus_eq_of_mem_dom hcover h (hsAn e' P he')]

include hcover hsC hsAn in

theorem support_smul_subset_dom {i : Fin n} (D : Divisor L F)
    (hD : ∀ P ∈ D.support, P ∈ (C i).dom) : ∀ P ∈ (s • D).support, P ∈ (C i).dom := by
  intro P hP
  rw [mem_support_smul_iff] at hP
  have h := hD _ hP
  rw [mem_dom_iff_smul_mem_dom hcover s hsC hsAn i, smul_inv_smul] at h
  exact h

include hcover hsC hsAn in

theorem support_smul_subset_annulus {e : Fin m} (D : Divisor L F)
    (hD : ∀ P ∈ D.support, P ∈ (An e).dom) : ∀ P ∈ (s • D).support, P ∈ (An e).dom := by
  intro P hP
  rw [mem_support_smul_iff] at hP
  have h := hD _ hP
  rw [mem_annulus_iff_smul_mem_annulus hcover s hsC hsAn e, smul_inv_smul] at h
  exact h

include hcover hsC hsAn in

theorem smul_sub_self_chart {i : Fin n}
    (hspm : ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P) (D : Divisor L F)
    (hD : ∀ P ∈ D.support, P ∈ (C i).dom) :
    (∀ P ∈ (s • D - D).support, P ∈ (C i).dom) ∧ Divisor.degree (s • D - D) = 0 ∧
      Finsupp.mapDomain (C i).placeMap (s • D - D) = 0 := by
  classical
  refine ⟨fun P hP => ?_, ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finsupp.support_sub hP) with h | h
    · exact support_smul_subset_dom hcover s hsC hsAn D hD P h
    · exact hD P h
  · rw [map_sub, SemilinearAut.degree_smul, sub_self]
  · rw [mapDomain_sub', mapDomain_smul_eq_of_forall _ s D (fun P hP => hspm P (hD P hP)), sub_self]

include hcover hsC hsAn in

theorem smul_sub_self_annulus {e : Fin m} (hsz : s • (An e).param = (An e).param)
    (hiso : ∀ a : L, a ≠ 0 → A.valuation (SemilinearAut.baseAut s a) = A.valuation a)
    (D : Divisor L F) (hD : ∀ P ∈ D.support, P ∈ (An e).dom) :
    (∀ P ∈ (s • D - D).support, P ∈ (An e).dom) ∧ ((s • D - D).sum fun _ k => k) = 0 ∧
      ((s • D - D).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) = 1 := by
  classical
  have hsD := support_smul_subset_annulus hcover s hsC hsAn D hD
  refine ⟨fun P hP => ?_, ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finsupp.support_sub hP) with h | h
    · exact hsD P h
    · exact hD P h
  · rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), sum_smul, sub_self]
  · rw [prod_zpow_sub _ _ _ (fun P hP => valuation_evalAt_ne_zero (An e) (hsD P hP))
      (fun P hP => valuation_evalAt_ne_zero (An e) (hD P hP)), prod_smul]
    have hX : (D.prod fun P k => A.valuation ((s • P).evalAt (An e).param) ^ k) =
        D.prod fun P k => A.valuation (P.evalAt (An e).param) ^ k := by
      refine Finset.prod_congr rfl fun P hP => ?_
      have hPd : P ∈ (An e).dom := hD P hP
      obtain ⟨hrat, hzP, -, hne, -⟩ := (An e).mem_dom P hPd
      obtain ⟨hrat', -⟩ := (An e).mem_dom (s • P) (hsAn e P hPd)
      show A.valuation ((s • P).evalAt (An e).param) ^ (D P) = A.valuation (P.evalAt (An e).param) ^ (D P)
      rw [evalAt_smul_of_smul_eq s P hrat hrat' hzP hsz, hiso _ hne]
    rw [hX]
    refine mul_inv_cancel₀ ?_
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun P hP =>
      zpow_ne_zero _ (valuation_evalAt_ne_zero (An e) (hD P hP))

include hcover in

theorem eq_sum_filter_add_sum_filter [DecidableEq (Place L F)] (E : Divisor L F)
    [∀ i, DecidablePred (· ∈ (C i).dom)] [∀ e, DecidablePred (· ∈ (An e).dom)] :
    E = ∑ i, E.filter (· ∈ (C i).dom) + ∑ e, E.filter (· ∈ (An e).dom) := by
  ext P
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.filter_apply]
  rcases hcover P with ⟨i, hi, huniq, hno⟩ | ⟨e, he, huniq, hno⟩
  · rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (huniq j h))
        (fun h => (h (Finset.mem_univ i)).elim), if_pos hi,
      Finset.sum_eq_zero (fun e _ => if_neg (hno e)), add_zero]
  · rw [Finset.sum_eq_zero (fun j _ => if_neg (hno j)),
      Finset.sum_eq_single e (fun e' _ hne => if_neg fun h => hne (huniq e' h))
        (fun h => (h (Finset.mem_univ e)).elim), if_pos he, zero_add]

include hcover hsC hsAn in

theorem isNull_smul_sub
    (hspm : ∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P)
    (hsz : ∀ e, s • (An e).param = (An e).param)
    (hiso : ∀ a : L, a ≠ 0 → A.valuation (SemilinearAut.baseAut s a) = A.valuation a)
    (c : Pic0 L F) : IsNull C An (s • c - c) := by
  classical
  obtain ⟨⟨E, hE⟩, rfl⟩ := Pic0.mk_surjective c
  set Ec : Fin n → Divisor L F := fun i => E.filter (· ∈ (C i).dom) with hEc
  set Ea : Fin m → Divisor L F := fun e => E.filter (· ∈ (An e).dom) with hEa
  have hsplitE : E = ∑ i, Ec i + ∑ e, Ea e := eq_sum_filter_add_sum_filter hcover E
  have hEcdom : ∀ i, ∀ P ∈ (Ec i).support, P ∈ (C i).dom := by
    intro i P hP
    rw [hEc, Finsupp.support_filter, Finset.mem_filter] at hP
    exact hP.2
  have hEadom : ∀ e, ∀ P ∈ (Ea e).support, P ∈ (An e).dom := by
    intro e P hP
    rw [hEa, Finsupp.support_filter, Finset.mem_filter] at hP
    exact hP.2
  set T : Divisor.degZero (K := L) (F := F) := SemilinearAut.degZeroSMulHom s ⟨E, hE⟩ - ⟨E, hE⟩
    with hT
  have hTcoe : (T : Divisor L F) = s • E - E := rfl
  have hchart := fun i => smul_sub_self_chart hcover s hsC hsAn (hspm i) (Ec i) (hEcdom i)
  have hann := fun e => smul_sub_self_annulus hcover s hsC hsAn (hsz e) hiso (Ea e) (hEadom e)
  refine ⟨(T : Divisor L F), T.2, fun i => s • Ec i - Ec i, fun e => s • Ea e - Ea e, ?_, ?_,
    fun i => (hchart i).1, fun i => (hchart i).2.1, fun i => (hchart i).2.2,
    fun e => (hann e).1, fun e => (hann e).2.1, fun e => (hann e).2.2⟩
  · rw [smul_mk_sub_mk]
  · rw [hTcoe]
    calc s • E - E = s • (∑ i, Ec i + ∑ e, Ea e) - (∑ i, Ec i + ∑ e, Ea e) := by rw [← hsplitE]
      _ = (∑ i, s • Ec i - ∑ i, Ec i) + (∑ e, s • Ea e - ∑ e, Ea e) := by
          rw [smul_add, Finset.smul_sum, Finset.smul_sum]; abel
      _ = ∑ i, (s • Ec i - Ec i) + ∑ e, (s • Ea e - Ea e) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

end Null
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate"

namespace Levels

open Null

variable {L : Type} [Field L] {A : ValuationSubring L} {F : Type} [Field F] [Algebra L F]
variable {n m : ℕ} {Fbar : Fin n → Type*} [∀ i, Field (Fbar i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
variable {C : ∀ i, ComponentChart A F (Fbar i)} {An : Fin m → Annulus A F}

theorem proj_rep_sub (ℓ : ℕ) [Fact ℓ.Prime]
    (s : SemilinearAut L F) (x : TateModule ℓ (Pic0 L F)) (k : ℕ) :
    TateModule.proj ℓ (Pic0 L F) k (TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) s x - x) =
      s • TateModule.proj ℓ (Pic0 L F) k x - TateModule.proj ℓ (Pic0 L F) k x := by
  rw [map_sub]; rfl

theorem isNull_proj_of_mem_span (ℓ : ℕ) [Fact ℓ.Prime] (S : Set (SemilinearAut L F))
    (hgen : ∀ s ∈ S, ∀ c : Pic0 L F, IsNull C An (s • c - c))
    {y : TateModule ℓ (Pic0 L F)}
    (hy : y ∈ Submodule.span ℤ_[ℓ]
      {t | ∃ s ∈ S, ∃ x, t = TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) s x - x})
    (k : ℕ) : IsNull C An (TateModule.proj ℓ (Pic0 L F) k y) := by
  induction hy using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨s, hs, x, rfl⟩ := ht
    rw [proj_rep_sub]
    exact hgen s hs _
  | zero => rw [map_zero]; exact isNull_zero
  | add t t' _ _ ht ht' => rw [map_add]; exact isNull_add ht ht'
  | smul a t _ ht => rw [Tate.proj_smul]; exact isNull_nsmul ht _

end Levels
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate"

namespace Core

open Null IsLocalRing

theorem mapDomain_mem_principal_of_isNull
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
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
    {c : Pic0 L F} (hc : IsNull C An c)
    (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (hmk : Pic0.mk ⟨D, hD⟩ = c)
    (Di : Fin n → Divisor L F) (hsum : D = ∑ i, Di i)
    (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) (hdeg : ∀ i, Divisor.degree (Di i) = 0) :
    ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
      Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) := by
  classical
  obtain ⟨D', hD', Dc, Ne, hmk', hsplit, hDcdom, hDcdeg, hDcmap, hNedom, hNesum, hNeprod⟩ := hc

  have hpr : D - D' ∈ Divisor.principal (K := L) (F := F) := by
    have h : (Pic0.mk ⟨D, hD⟩ : Pic0 L F) = Pic0.mk ⟨D', hD'⟩ := hmk.trans hmk'.symm
    have h' := (QuotientAddGroup.eq (s := (Divisor.principal (K := L) (F := F)).addSubgroupOf
      (Divisor.degZero (K := L) (F := F)))).mp h
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg] at h'
    have h'' : -(D - D') ∈ Divisor.principal (K := L) (F := F) := by
      have : -(D - D') = -D + D' := by abel
      rw [this]; exact h'
    simpa using (Divisor.principal (K := L) (F := F)).neg_mem h''
  obtain ⟨f, hf0, hf⟩ := hpr

  have hDioff : ∀ j P, P ∉ (C j).dom → Di j P = 0 := fun j P hP => by
    by_contra h
    exact hP (hdom j P (Finsupp.mem_support_iff.mpr h))
  have hDcoff : ∀ j P, P ∉ (C j).dom → Dc j P = 0 := fun j P hP => by
    by_contra h
    exact hP (hDcdom j P (Finsupp.mem_support_iff.mpr h))
  have hNeoff : ∀ e P, P ∉ (An e).dom → Ne e P = 0 := fun e P hP => by
    by_contra h
    exact hP (hNedom e P (Finsupp.mem_support_iff.mpr h))

  have hDchart : ∀ i, ∀ P ∈ (C i).dom, D P = Di i P := by
    intro i P hP
    have hji : ∀ j, j ≠ i → Di j P = 0 := fun j hji =>
      hDioff j P fun hPj => hji (chart_eq_of_mem_dom hcover hPj hP)
    rw [hsum, Finsupp.finsetSum_apply,
      Finset.sum_eq_single i (fun j _ hj => hji j hj) (fun h => (h (Finset.mem_univ i)).elim)]
  have hD'chart : ∀ i, ∀ P ∈ (C i).dom, D' P = Dc i P := by
    intro i P hP
    have hji : ∀ j, j ≠ i → Dc j P = 0 := fun j hji =>
      hDcoff j P fun hPj => hji (chart_eq_of_mem_dom hcover hPj hP)
    have hne : ∀ e, Ne e P = 0 := fun e =>
      hNeoff e P fun hPe => not_mem_dom_of_mem_annulus hcover hP hPe
    rw [hsplit, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply,
      Finset.sum_eq_single i (fun j _ hj => hji j hj) (fun h => (h (Finset.mem_univ i)).elim),
      Finset.sum_eq_zero (fun e _ => hne e), add_zero]

  have hDann : ∀ e, ∀ P ∈ (An e).dom, D P = 0 := by
    intro e P hP
    rw [hsum, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun j _ =>
      hDioff j P fun hPj => not_mem_dom_of_mem_annulus hcover hPj hP
  have hD'ann : ∀ e, ∀ P ∈ (An e).dom, D' P = Ne e P := by
    intro e P hP
    have hj : ∀ j, Dc j P = 0 := fun j =>
      hDcoff j P fun hPj => not_mem_dom_of_mem_annulus hcover hPj hP
    have hne : ∀ e', e' ≠ e → Ne e' P = 0 := fun e' he' =>
      hNeoff e' P fun hPe => he' (annulus_eq_of_mem_dom hcover hPe hP)
    rw [hsplit, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply,
      Finset.sum_eq_zero (fun j _ => hj j),
      Finset.sum_eq_single e (fun e' _ he' => hne e' he') (fun h => (h (Finset.mem_univ e)).elim),
      zero_add]

  have key :=
    AlgebraicCurve.mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
      A π hπ hπ0 F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes f hf0
      (fun i => Di i - Dc i)
      (fun i P hP => by
        rcases Finset.mem_union.mp (Finsupp.support_sub hP) with h | h
        · exact hdom i P h
        · exact hDcdom i P h)
      (fun i P hP => by
        rw [Finsupp.sub_apply, ← hDchart i P hP, ← hD'chart i P hP, ← Finsupp.sub_apply, hf P])
      (fun i => by rw [map_sub, hdeg, hDcdeg, sub_zero])
      (fun e => -Ne e)
      (fun e P hP => by
        rw [Finsupp.support_neg] at hP
        exact hNedom e P hP)
      (fun e P hP => by
        rw [Finsupp.neg_apply, ← hf P, Finsupp.sub_apply, hDann e P hP, hD'ann e P hP, zero_sub])
      (fun e => by rw [sum_neg', hNesum, neg_zero])
      (fun e => by rw [prod_zpow_neg, hNeprod, inv_one])
  intro i
  have h := key i
  have hDi : Di i = (Di i - Dc i) + Dc i := (sub_add_cancel _ _).symm
  rw [hDi, Finsupp.mapDomain_add, hDcmap, add_zero]
  exact h

end Core
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate"

end MonodromyDiesEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine.Tate P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.MonodromyDiesEngine"

open scoped TensorProduct

open AlgebraicCurve

set_option maxHeartbeats 3200000 in
open MonodromyDiesEngine in

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
    :
    ∀ v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈ Submodule.span ℚ_[ℓ] {u | ∃ s ∈ S, ∃ w,
        u = ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s w - w} →
        red v = 0 := by
  intro v hv

  have hiso : ∀ s ∈ S, ∀ a : L, a ≠ 0 →
      A.valuation (SemilinearAut.baseAut s a) = A.valuation a := by
    intro s hs a ha
    obtain ⟨u, hu⟩ :=
      ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne A π hπ hπ0 hrk
        (SemilinearAut.baseAut s) (hS s hs).1 (hS s hs).2.1 a ha
    rw [hu, map_mul, A.valuation_unit u, one_mul]

  have hgen : ∀ s ∈ S, ∀ c : Pic0 L F, Null.IsNull C An (s • c - c) := by
    intro s hs c
    obtain ⟨-, -, -, hsC, hsAn, hsz, -, -, hspm⟩ := hS s hs
    exact Null.isNull_smul_sub hcover s hsC hsAn hspm hsz (hiso s hs) c

  obtain ⟨a, y, ha, hy, hav⟩ := SpanClear.exists_clear S (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) hv
  obtain ⟨v', hv'def⟩ : ∃ v' : ↥(⨅ s ∈ S, LinearMap.ker
      (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)), v' = (a : ℚ_[ℓ]) • v :=
    ⟨_, rfl⟩
  have hv' : (v' : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y := by
    rw [hv'def, Submodule.coe_smul]; exact hav
  suffices h : red v' = 0 by
    have h1 : (a : ℚ_[ℓ]) • red v = 0 := by rw [← map_smul, ← hv'def]; exact h
    exact (smul_eq_zero.mp h1).resolve_left (PadicInt.coe_ne_zero.mpr ha)

  have hlevel : ∀ k i, ∃ y' : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
      red v' i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y' ∧
        TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y' = 0 := by
    intro k i
    obtain ⟨D, hD, Di, hmk, hsum, hdom, hdeg⟩ :=
      AlgebraicCurve.exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc
        hgenus S hS hSlift ℓ hℓ hSℓ M D v' y hv' k
    obtain ⟨y', hy', hE⟩ := hred v' y hv' k D hD hmk Di hsum hdom hdeg i
    have hnull : Null.IsNull C An (TateModule.proj ℓ (Pic0 L F) k y) :=
      Levels.isNull_proj_of_mem_span ℓ S hgen hy k
    have hprin : Finsupp.mapDomain (C i).placeMap (Di i) ∈
        Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) :=
      Core.mapDomain_mem_principal_of_isNull A π hπ hπ0 F n m Fbar hratBar C hratF An An' src tgt xs xt
        w hpair hw hatt hnodes hcover hnull D hD hmk Di hsum hdom hdeg i
    obtain ⟨g, hg0, hg⟩ := hprin
    obtain ⟨Eg, hEg, hEgdeg⟩ :=
      HasPrincipalDivisors.exists_divisor (K := IsLocalRing.ResidueField A) g hg0
    have hEeq : Eg = Finsupp.mapDomain (C i).placeMap (Di i) := Finsupp.ext fun Q => by
      rw [hEg Q, hg Q]
    have hdeg0 : Finsupp.mapDomain (C i).placeMap (Di i) ∈
        Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i) := by
      rw [Divisor.mem_degZero, ← hEeq]; exact hEgdeg
    refine ⟨y', hy', ?_⟩
    rw [hE ⟨_, hdeg0⟩ rfl]
    show (QuotientAddGroup.mk _ : Pic0 (IsLocalRing.ResidueField A) (Fbar i)) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨g, hg0, hg⟩

  refine funext fun i => ?_
  refine (hlevel 0 i).elim fun y' hy0' => ?_
  have hyk : ∀ k, TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y' = 0 :=
    fun k => (hlevel k i).elim fun y'' h => by
      have : y' = y'' := Tate.one_tmul_injective (hy0'.1.symm.trans h.1)
      rw [this]; exact h.2
  have hy0 : y' = 0 := Subtype.ext (funext fun k => hyk k)
  rw [Pi.zero_apply, hy0'.1, hy0, TensorProduct.tmul_zero]

end S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
