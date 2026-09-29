-- Prove2me | solution 1 for AlgebraicCurve.Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0e6b3b52-56c7-5635-a18a-a5931b2809ae

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.AlgebraicCurve KaehlerDifferential IntermediateField Module Filter Topology"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.algebraMap_mem' IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.evalAt HasCanonicalDivisor canonicalDivisorOf genus FunctionFieldRiemannRoch LSpace ell mem_lSpace_iff_ord dCoordGenerates_of_isCurveOver IsCurveOver.exists_separating_transcendental isCurveOver_ratFunc essFiniteType_of_transcendental_of_finiteDimensional functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver hasCanonicalDivisor_of_isCurveOver Place.exists_ord_neg_of_transcendental"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_coe_eq_one_iff ord exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt DCoordGenerates adicValuation_le_one_of_mem adicValuation_eq_exp_neg_ord adicValuation_le_one_iff exists_ord_neg_of_transcendental"
namespace ConnectedOfCharted
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f := by
  have hle : v.adicValuation f ≤ 1 := v.adicValuation_le_one_of_mem hf
  have hne : v.adicValuation f ≠ 1 := by
    intro h1
    have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
      (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne
  rw [v.adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_algebraMap (v : Place K F) (c : K) : v.evalAt (algebraMap K F c) = c := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' c)]
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]
  exact v.residueInv_algebraMap c

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) :
    v.evalAt (f - algebraMap K F c) = v.evalAt f - c := by
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hfc, map_sub, v.algebraMap_evalAt hv hf]
  have h1 : (⟨f - algebraMap K F c, hfc⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap K F c, hc⟩ := rfl
  have h2 : IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, hc⟩
      = algebraMap K v.ResidueField c := by
    rw [← v.algebraMap_evalAt hv hc, evalAt_algebraMap]
  rw [h1, map_sub, h2]

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  refine ord_pos_of_mem_maximalIdeal v hf0 hf ?_
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hf, h0, map_zero]

theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    {w : Place K F | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine D.support.finite_toSet.subset fun w hw => ?_
  simpa [Finsupp.mem_support_iff, hD w] using hw

theorem functionFieldRiemannRoch [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    FunctionFieldRiemannRoch K F := by
  classical
  obtain ⟨t, ht, htfd, htsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := htfd
  haveI := htsep
  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  intro _ _ _ η hη D
  exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hη D

theorem exists_nonconst_mem_of_ne [IsAlgClosed K] [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] (v₀ : Place K F) :
    ∃ f : F, f ∉ Set.range (algebraMap K F) ∧
      ∀ w : Place K F, w ≠ v₀ → f ∈ w.toValuationSubring := by
  classical
  haveI : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨η, hη⟩ := exists_ne (0 : Ω[F⁄K])
  set D : Divisor K F := Finsupp.single v₀ ((genus K F : ℤ) + 1) with hD
  have hRR := functionFieldRiemannRoch (K := K) (F := F) hη D
  have hdeg : Divisor.degree D = (genus K F : ℤ) + 1 := by
    rw [hD, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed v₀]
    simp
  have hell : (2 : ℤ) ≤ (ell D : ℤ) := by
    have : (0 : ℤ) ≤ (ell (canonicalDivisorOf hη - D) : ℤ) := Nat.cast_nonneg _
    rw [hdeg] at hRR
    linarith

  have hnot : ¬ ((LSpace D : Set F) ⊆ Set.range (algebraMap K F)) := by
    intro hle
    have hle' : LSpace D ≤ LinearMap.range (Algebra.linearMap K F) := fun f hf => by
      obtain ⟨c, hc⟩ := hle hf
      exact ⟨c, hc⟩
    haveI : Module.Finite K (LinearMap.range (Algebra.linearMap K F)) :=
      Module.Finite.range (Algebra.linearMap K F)
    have h1 : Module.finrank K (LSpace D)
        ≤ Module.finrank K (LinearMap.range (Algebra.linearMap K F)) :=
      Submodule.finrank_mono hle'
    have h2 : Module.finrank K (LinearMap.range (Algebra.linearMap K F)) ≤ 1 := by
      simpa using LinearMap.finrank_range_le (Algebra.linearMap K F)
    have h3 : (ell D : ℤ) ≤ 1 := by
      have : ell D ≤ 1 := h1.trans h2
      exact_mod_cast this
    linarith
  obtain ⟨f, hfL, hfc⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfc, fun w hw => ?_⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hfc ⟨0, by simp⟩
  have hford := ((mem_lSpace_iff_ord (D := D)).mp hfL).resolve_left hf0 w
  have hDw : D w = 0 := by
    rw [hD, Finsupp.single_apply, if_neg (fun h => hw h.symm)]
  exact mem_of_ord_nonneg w hf0 (by simpa [hDw] using hford)

section Analytic

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def reading (v : Place ℂ F) (f : F) : ℂ → ℂ :=
  fun z => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f

variable (F) in

def OrderHypothesis : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

omit [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] in
theorem evalAt_zero' (w : Place ℂ F) : w.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap w (0 : ℂ)

theorem reading_center (v : Place ℂ F) (f : F) :
    reading v f (extChartAt 𝓘(ℂ, ℂ) v v) = v.evalAt f := by
  simp [reading]

theorem eventually_mem_chart (v : Place ℂ F) {f : F}
    (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
  have hc := continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v
  rw [ContinuousAt, extChartAt_to_inv] at hc
  exact hc.eventually hreg

theorem tendsto_reading [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F) {f : F}
    (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    Tendsto (reading v f) (𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)) (𝓝 (v.evalAt f)) := by
  set c := v.evalAt f with hc_def
  have hv : f ∈ v.toValuationSubring := hreg.self_of_nhds
  have hrat : ∀ w : Place ℂ F, w.IsRational := isRational_of_isAlgClosed
  have heq : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
      reading v (f - algebraMap ℂ F c) z = reading v f z - c := by
    refine ((eventually_mem_chart v hreg).filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_
    exact evalAt_sub_algebraMap _ (hrat _) hz c
  by_cases h0 : f - algebraMap ℂ F c = 0
  · have hcst : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v), reading v f z = c := by
      refine heq.mono fun z hz => ?_
      rw [h0] at hz
      have : reading v (0 : F) z = 0 := evalAt_zero' _
      rw [this] at hz
      exact (sub_eq_zero.mp hz.symm)
    exact tendsto_const_nhds.congr' (hcst.mono fun z hz => hz.symm)
  · have hpos : 0 < v.ord (f - algebraMap ℂ F c) := by
      refine ord_pos_of_evalAt_eq_zero v (hrat v) h0 (sub_mem hv (v.algebraMap_mem' c)) ?_
      rw [evalAt_sub_algebraMap v (hrat v) hv c, hc_def, sub_self]
    have hordW : (0 : WithTop ℤ) <
        meromorphicOrderAt (reading v (f - algebraMap ℂ F c)) (extChartAt 𝓘(ℂ, ℂ) v v) := by
      rw [(hF _ h0 v).2]
      exact_mod_cast hpos
    have ht := tendsto_zero_of_meromorphicOrderAt_pos hordW
    have ht' : Tendsto (fun z => reading v f z - c) (𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)) (𝓝 0) :=
      ht.congr' heq
    have := ht'.add (tendsto_const_nhds (x := c))
    simpa only [sub_add_cancel, zero_add] using this

theorem continuousAt_reading [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F) {f : F}
    (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    ContinuousAt (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, reading_center]
  exact tendsto_reading hF v hreg

theorem analyticAt_reading [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F) {f : F}
    (hf0 : f ≠ 0) (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    AnalyticAt ℂ (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) :=
  (hF f hf0 v).1.analyticAt (continuousAt_reading hF v hreg)

theorem continuousAt_evalAt [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F) {f : F}
    (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    ContinuousAt (fun w : Place ℂ F => w.evalAt f) v := by
  have h1 : ContinuousAt (reading v f ∘ extChartAt 𝓘(ℂ, ℂ) v) v :=
    ContinuousAt.comp (continuousAt_reading hF v hreg) (continuousAt_extChartAt v)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) v] with w hw
  simp only [Function.comp_apply, reading, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]

theorem false_of_isClopen [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [CompactSpace (Place ℂ F)] (hF : OrderHypothesis F)
    {U : Set (Place ℂ F)} (hU : IsClopen U) (v₀ : Place ℂ F) (hv₀ : v₀ ∈ U)
    (hne : Uᶜ.Nonempty) : False := by
  have hrat : ∀ w : Place ℂ F, w.IsRational := isRational_of_isAlgClosed
  obtain ⟨f, hfc, hfreg⟩ := exists_nonconst_mem_of_ne (K := ℂ) (F := F) v₀
  have hf0 : f ≠ 0 := fun h => hfc ⟨0, by simp [h]⟩
  have hVo : IsOpen Uᶜ := hU.compl.isOpen
  have hVc : IsCompact Uᶜ := hU.compl.isClosed.isCompact
  have hregV : ∀ w ∈ Uᶜ, f ∈ w.toValuationSubring := fun w hw =>
    hfreg w (fun h => hw (h ▸ hv₀))
  have hev : ∀ w ∈ Uᶜ, ∀ᶠ w' in 𝓝 w, f ∈ w'.toValuationSubring := fun w hw =>
    Filter.eventually_of_mem (hVo.mem_nhds hw) hregV

  have hcont : ContinuousOn (fun w : Place ℂ F => ‖w.evalAt f‖) Uᶜ := fun w hw =>
    ((continuousAt_evalAt hF w (hev w hw)).norm).continuousWithinAt
  obtain ⟨w₀, hw₀, hmax⟩ := hVc.exists_isMaxOn hne hcont
  have hloc : IsLocalMax (fun w : Place ℂ F => ‖w.evalAt f‖) w₀ :=
    hmax.isLocalMax (hVo.mem_nhds hw₀)

  have hsymm : Tendsto (extChartAt 𝓘(ℂ, ℂ) w₀).symm (𝓝 (extChartAt 𝓘(ℂ, ℂ) w₀ w₀)) (𝓝 w₀) := by
    have hc := continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w₀
    rwa [ContinuousAt, extChartAt_to_inv] at hc
  have hloc' : IsLocalMax (norm ∘ reading w₀ f) (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) := by
    have h1 : IsMaxFilter (fun w : Place ℂ F => ‖w.evalAt f‖)
        (𝓝 ((extChartAt 𝓘(ℂ, ℂ) w₀).symm (extChartAt 𝓘(ℂ, ℂ) w₀ w₀)))
        ((extChartAt 𝓘(ℂ, ℂ) w₀).symm (extChartAt 𝓘(ℂ, ℂ) w₀ w₀)) := by
      rw [extChartAt_to_inv]; exact hloc
    have h2 := h1.comp_tendsto (by rw [extChartAt_to_inv]; exact hsymm)
    exact h2
  have han : AnalyticAt ℂ (reading w₀ f) (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) :=
    analyticAt_reading hF w₀ hf0 (hev w₀ hw₀)
  have hdiff : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w₀ w₀), DifferentiableAt ℂ (reading w₀ f) z :=
    han.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hconst := Complex.eventually_eq_of_isLocalMax_norm hdiff hloc'
  set c := reading w₀ f (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) with hc_def

  set S : Set ℂ := {z | z ∈ (extChartAt 𝓘(ℂ, ℂ) w₀).target ∧
    (extChartAt 𝓘(ℂ, ℂ) w₀).symm z ∈ Uᶜ ∧ reading w₀ f z = c} with hS_def
  have hS : S ∈ 𝓝 (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) w₀,
      hsymm.eventually_mem (hVo.mem_nhds hw₀), hconst] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hSinf : S.Infinite := infinite_of_mem_nhds _ hS
  have hinj : Set.InjOn (extChartAt 𝓘(ℂ, ℂ) w₀).symm S := fun a ha b hb h => by
    have := congrArg (extChartAt 𝓘(ℂ, ℂ) w₀) h
    rwa [(extChartAt 𝓘(ℂ, ℂ) w₀).right_inv ha.1, (extChartAt 𝓘(ℂ, ℂ) w₀).right_inv hb.1]
      at this
  have himg : ((extChartAt 𝓘(ℂ, ℂ) w₀).symm '' S).Infinite := hSinf.image hinj

  have hg0 : f - algebraMap ℂ F c ≠ 0 := fun h => hfc ⟨c, (sub_eq_zero.mp h).symm⟩
  refine himg ((finite_setOf_ord_ne_zero (K := ℂ) hg0).subset ?_)
  rintro w ⟨z, hz, rfl⟩
  have hw : f ∈ ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z).toValuationSubring := hregV _ hz.2.1
  have hpos : 0 < ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z).ord (f - algebraMap ℂ F c) := by
    refine ord_pos_of_evalAt_eq_zero _ (hrat _) hg0 (sub_mem hw (Place.algebraMap_mem' _ c)) ?_
    rw [evalAt_sub_algebraMap _ (hrat _) hw c]
    exact sub_eq_zero.mpr hz.2.2
  exact hpos.ne'

end Analytic

end AlgebraicCurve.Place.ConnectedOfCharted

end

open scoped Manifold ContDiff Topology

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.AlgebraicCurve AlgebraicCurve.Place.ConnectedOfCharted in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [CompactSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)) :
    ConnectedSpace (Place ℂ F) := by
  obtain ⟨x, hx, hxfd⟩ := hfg
  haveI := hxfd
  haveI : Algebra.EssFiniteType ℂ F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  have hF' : OrderHypothesis F := hF

  obtain ⟨v₁, -⟩ := Place.exists_ord_neg_of_transcendental (K := ℂ) x hx
  haveI : Nonempty (Place ℂ F) := ⟨v₁⟩

  have hpre : PreconnectedSpace (Place ℂ F) := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    by_contra hcon
    obtain ⟨hne, hnu⟩ := not_or.mp hcon
    obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hcne : Uᶜ.Nonempty := Set.nonempty_compl.mpr hnu
    exact false_of_isClopen hF' hU v₀ hv₀ hcne
  exact { toPreconnectedSpace := hpre, toNonempty := inferInstance }

end S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex
end P2MW
export P2MW.S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex (solution)
