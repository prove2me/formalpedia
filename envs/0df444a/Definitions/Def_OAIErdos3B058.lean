-- Prove2me | Definitions.Def_OAIErdos3B058
-- name    : OAIErdos3B058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T06:33:09.624243+00:00
-- url     : https://prove2.me/theorems/d8a72697-bf4d-455d-a0a7-702762b7fbc5
-- title:
--   OpenAI Erdős-3 split, definitions bundle 59 of 187
-- statement:
--   Definitions bundle 59 of 187 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B057`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 59 available.
--
--   Modules: `OAI.Erdos3.DegreeRankLieFiltration.exists_controlled_horizontal_lifts`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalPreimage`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalPreimage_coordinates`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalPreimage_le`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalPreimage_mono`, `OAI.Erdos3.DegreeRankLieFiltration.mem_horizontalPreimage`, `OAI.Erdos3.DegreeRankLieFiltration.mem_real_horizontalPreimage`, `OAI.Erdos3.DegreeRankLieFiltration.nativeHorizontalCoefficientHom_eq_realHorizontalMap`, `OAI.Erdos3.DegreeRankLieFiltration.native_coefficient_mem_horizontalPreimage`, `OAI.Erdos3.DegreeRankLieFiltration.polynomialOrbit_coefficient_mem_rank_one`, `OAI.Erdos3.DegreeRankLieFiltration.polynomialOrbit_log_mul_mod_rank_two`, `OAI.Erdos3.DegreeRankLieFiltration.rankLayerCoefficient_tensor_coe`, `OAI.Erdos3.DegreeRankLieFiltration.rankLayerCoefficient_tensor_horizontal`, `OAI.Erdos3.DegreeRankLieFiltration.realFourLayerComponent`, `OAI.Erdos3.DegreeRankLieFiltration.realFourLayerComponent_coe`, `OAI.Erdos3.DegreeRankLieFiltration.realFourLayerComponent_grid`, `OAI.Erdos3.DegreeRankLieFiltration.realFourLayerComponent_horizontal`, `OAI.Erdos3.DegreeRankLieFiltration.realFourLayerComponent_norm_bound`, `OAI.Erdos3.DegreeRankLieFiltration.realHigherHorizontalCoordinates_map`, `OAI.Erdos3.DegreeRankLieFiltration.realHigherHorizontalCoordinates_mem`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalMap`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalMap_ambient`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalMap_baseChange`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalMap_eq`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalMap_surjective`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalRepresentative`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalRepresentative_zero`, `OAI.Erdos3.NativeDegreeRankFamily.fourPointFactors`, `OAI.Erdos3.NativeDegreeRankFamily.fourPointFactors_complexity`, `OAI.Erdos3.NativeDegreeRankFamily.fourPointFactors_eval`, `OAI.Erdos3.NativeDegreeRankFamily.fourPointFactors_orbit`, `OAI.Erdos3.NativeDegreeRankFamily.fourPointFactors_vertical`, `OAI.Erdos3.NativeDegreeRankFamily.fourPointFrequencies`, `OAI.Erdos3.NativeDegreeRankFamily.fourPoint_horizontalCoefficient`, `OAI.Erdos3.NativeDegreeRankFamily.fourRankBasis`, `OAI.Erdos3.NativeDegreeRankFamily.horizontalCoefficient`, `OAI.Erdos3.NativeDegreeRankFamily.horizontalCoefficient_real_log`, `OAI.Erdos3.NativeDegreeRankFamily.logCoefficient_mem_rank_one`, `OAI.Erdos3.NativeRankInterval.BracketKernel`, `OAI.Erdos3.NativeRankInterval.SunflowerKernel`, `OAI.Erdos3.NativeRankInterval.productFrequencies`, `OAI.Erdos3.NativeRankInterval.productModels`, `OAI.Erdos3.NativeRankInterval.productOrbit`, `OAI.Erdos3.NativeRankInterval.productRanks`, `OAI.Erdos3.NativeRankInterval.productSymbol`, `OAI.Erdos3.NativeRankInterval.productSymbol_eq`, `OAI.Erdos3.NativeRankInterval.productTests`, `OAI.Erdos3.NativeRankInterval.productTests_eval`, `OAI.Erdos3.NativeRankInterval.productTests_vertical`, `OAI.Erdos3.NativeRankInterval.projectedCoefficient`, `OAI.Erdos3.NativeRankInterval.rankProjection`, `OAI.Erdos3.NativeRankInterval.rankProjection_coefficient`, `OAI.Erdos3.NativeRankInterval.rankProjection_component_log`, `OAI.Erdos3.NativeRankInterval.rankProjection_coordinates`, `OAI.Erdos3.NativeRankInterval.rankProjection_coordinates_logHeight`, `OAI.Erdos3.NativeRankInterval.rankProjection_frequency`, `OAI.Erdos3.NativeRankInterval.rankProjection_mem_layer`, `OAI.Erdos3.NativeRankInterval.rankProjection_mem_refiltered`, `OAI.Erdos3.NativeRankInterval.real_rankProjection_abs_bound`, `OAI.Erdos3.NativeRankInterval.real_rankProjection_coordinates`, `OAI.Erdos3.NativeRankInterval.real_rankProjection_grid`, `OAI.Erdos3.NativeRankInterval.refilteredHorizontalImage`, `OAI.Erdos3.NativeRankInterval.refilteredHorizontalImage_eq`, `OAI.Erdos3.NativeRankInterval.refilteredHorizontalImage_frequency`, `OAI.Erdos3.NativeRankInterval.refilteredProjectionImage`, `OAI.Erdos3.NativeRankInterval.refilteredProjectionImage_mem_candidates`, `OAI.Erdos3.NativeRankInterval.refiltered_sunflower_bracket`, `OAI.Erdos3.NativeRankInterval.sunflowerKernel_of_real`, `OAI.Erdos3.NilpotentLieFiltration.exists_actual_path_common_quotient_splitting`, `OAI.Erdos3.NilpotentLieFiltration.exists_actual_path_current_grade_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_restricted_path_common_quotient_splitting`, `OAI.Erdos3.NilpotentLieFiltration.orbitEquivOfEq_log`, `OAI.Erdos3.NilpotentLieFiltration.orbitEquivOfEq_translate`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_basisGraded`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_controlled_horizontal_representatives`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_horizontal_ambient_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_rank_two_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.orbitEquiv_log`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.orbitEquiv_translate`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.orbit_log_mul_mod_rank_two`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_biased_mode_restricting_frequency`, `OAI.Erdos3.RationalFilteredNilmanifold.piNiltest_rank_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.piRank`, `OAI.Erdos3.RationalFilteredNilmanifold.piRank_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.productObservable_rank_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjectionHom_mem_rank`, `OAI.Erdos3.RationalFilteredNilmanifold.productRankLayerBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.productRankLayerBasis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.productRankLayerFinBasis`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_native_approximation_with_budget`, `OAI.Erdos3.allocatedModelTestLog`, `OAI.Erdos3.allocatedModelUnitThreshold`, `OAI.Erdos3.allocatedModel_size_bounds`, `OAI.Erdos3.card_selected_four_le`, `OAI.Erdos3.exists_actual_path_reset_budget`, `OAI.Erdos3.exists_common_rank_relation_budget`, `OAI.Erdos3.exists_native_common_rank_budget`, `OAI.Erdos3.exists_rank_adapted_factorization_budget`, `OAI.Erdos3.exists_rank_biased_factorization_budget`, `OAI.Erdos3.exists_rank_biased_refiltration`, `OAI.Erdos3.exists_rank_biased_symbol_factorization`, `OAI.Erdos3.exists_rank_common_data_budget`, `OAI.Erdos3.exists_rank_interval_factorization`, `OAI.Erdos3.exists_rank_interval_product`, `OAI.Erdos3.exists_rank_interval_product_budget`, `OAI.Erdos3.exists_rank_interval_sunflower`, `OAI.Erdos3.exists_rank_unadapted_factorization`, `OAI.Erdos3.rankCoordinateTuple`, `OAI.Erdos3.rankCoordinateTuple_first12`, `OAI.Erdos3.rankCoordinateTuple_first13`, `OAI.Erdos3.rankCoordinateTuple_fixed12`, `OAI.Erdos3.rankCoordinateTuple_fixed13`, `OAI.Erdos3.rankIntervalInputBudget`, `OAI.Erdos3.rankIntervalInputBudget_bounds`, `OAI.Erdos3.rankQuadrupleParameters`, `OAI.Erdos3.rankVerticalSelectionBudget`, `OAI.Erdos3.rankVerticalSelectionBudget_bounds`, `OAI.Erdos3.rational_lieTree_kernel_of_real`, `OAI.Erdos3.real_firstProjection_mem`, `OAI.Erdos3.realifyFunctional_lieTreeEval_rational`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B157

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualPathCurrentGradeReset
namespace OAI

section

namespace Erdos3

theorem exists_actual_path_reset_budget (a cr cs ct : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let z := (p + cr) ^ cr + (p + 2) ^ a + p + 2
      (p + cr) ^ cr ≤ (p + C) ^ C ∧
        (z + cs) ^ cs ≤ (p + C) ^ C ∧
        (z + ct) ^ ct ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C cr) ^ cr
  let Z : Polynomial ℕ := P + (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let S : Polynomial ℕ := (Z + Polynomial.C cs) ^ cs
  let T : Polynomial ℕ := (Z + Polynomial.C ct) ^ ct
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + S + T)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hbound := hbudget p hp
  have hP := natPolynomial_eval_nonneg P hp
  have hS := natPolynomial_eval_nonneg S hp
  have hT := natPolynomial_eval_nonneg T hp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add] at hbound
  have hparts : P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      S.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      T.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C :=
    ⟨by linarith, by linarith, by linarith⟩
  simpa only [P, Z, S, T, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom, Nat.cast_ofNat] using hparts

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolPointwiseSubalgebra_basisGraded [Fintype τ] [Fintype ι]
    (v : τ → ℕ) (hv : ∀ i, 0 < v i) (U : LieSubalgebra ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.polynomialSymbolBasis b ω hF v)
      (fun z => ω z.val.2) (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule := by
  let : Fintype (SymbolBasisIndex v ω) :=
    symbolBasisIndexFintype v ω s hv (F.adaptedBasis_weight_le_step b ω hF)
  have h := (F.symbolPointwiseSubalgebra_blockInvariant b ω hF v U).graded
    (F.polynomialSymbolBasis b ω hF v) (fun z => z.val.1)
    (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule (Finsupp.weight v)
  have he : (fun z : SymbolBasisIndex v ω => Finsupp.weight v z.val.1) =
      (fun z => ω z.val.2) := funext (fun z => z.property)
  rw [he] at h
  exact h

theorem exists_restricted_path_common_quotient_splitting
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈
        realificationLieSubalgebra U)
    (El Pl Rl : F.RealPolynomialSymbolGroup v)
    (hlocal : El * Pl * Rl = F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ Z) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    ∃ P₀ : F.RealPolynomialSymbolGroup v,
      F.realSymbolGradeQuotientHom v k P₀ ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
          (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) ∧
      pull E * P₀ * pull R = El * Pl * Rl := by
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
  refine ⟨(pull E)⁻¹ * pull Z * (pull R)⁻¹,
    F.homogeneousPullback_residual_quotient_mem b ω hF w v β hβ U K hK E Z R k hx, ?_⟩
  rw [hlocal]
  change pull E * ((pull E)⁻¹ * pull Z * (pull R)⁻¹) * pull R = pull Z
  group

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_actual_path_common_quotient_splitting
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ,
      (fun i => MvPolynomial.eval u (weightedHomogeneousComponent v (w i) (β i))) ∈ K)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t
        (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U)
    (El Pl Rl : F.RealPolynomialSymbolGroup v)
    (hlocal : El * Pl * Rl = F.realPolynomialSymbolHom b ω hF v
      (F.weightedAdaptedRealChartHom w v β hβ g)) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
      (fun i => weightedHomogeneousComponent v (w i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    ∃ P₀ : F.RealPolynomialSymbolGroup v,
      F.realSymbolGradeQuotientHom v k P₀ ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
          (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) ∧
      pull E * P₀ * pull R = El * Pl * Rl := by
  have hactual := F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF w v β hβ g
  exact F.exists_restricted_path_common_quotient_splitting b ω hF w v
    (fun i => weightedHomogeneousComponent v (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    U K hK E (F.realPolynomialSymbolHom b ω hF w g) R k hx El Pl Rl (hlocal.trans hactual)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem exists_actual_path_current_grade_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (v : τ → ℕ), (∀ i, 0 < v i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : τ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded) (vg : κ → F.PolynomialSymbol v),
        Submodule.span ℚ (Set.range vg) = (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule →
        (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF v).repr (vg i) z) H) →
        ∀ {σ : Type*} (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ),
        ∀ hβ : ∀ i, β i ∈ weightedSupportLE v (w i),
        ∀ K : Set (σ → ℝ),
        (∀ u : τ → ℝ,
          (fun i => MvPolynomial.eval u (weightedHomogeneousComponent v (w i) (β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
          (E R : F.RealPolynomialSymbolGroup w) (k : ℕ), k ≤ s + 1 →
        (∀ t ∈ K, ∀ j < k, F.realSymbolGradeEvaluation b ω hF w j t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
          (fun i => weightedHomogeneousComponent v (w i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup v),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF v
          (F.weightedAdaptedRealChartHom w v β hβ g) →
        Pl.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF v l Rl → F.SymbolRationalGrid b ω hF v l (pull R) →
        ∃ E' P' R' : F.RealPolynomialSymbolGroup v,
          E' * P' * R' = F.realPolynomialSymbolHom b ω hF v
            (F.weightedAdaptedRealChartHom w v β hβ g) ∧
          P'.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) ∧
          F.realSymbolGradeQuotientHom v k (pull E) = F.realSymbolGradeQuotientHom v k E' ∧
          F.realSymbolGradeQuotientHom v k R' = F.realSymbolGradeQuotientHom v k (pull R) ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) E' ∧
          F.SymbolRationalGrid b ω hF v m R' ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) ((pull E)⁻¹ * E') ∧
          F.SymbolRationalGrid b ω hF v m (R' * (pull R)⁻¹) := by
  obtain ⟨cr, _, hreset⟩ := exists_symbol_reset_from_common_quotient s a
  obtain ⟨cs, _, hslowprod⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨ct, _, hratprod⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨C, hC, hbudget⟩ := exists_actual_path_reset_budget a cr cs ct
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T hT
  let z : ℝ := (p + cr) ^ cr + (p + 2) ^ a + p + 2
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpz : p ≤ z := by dsimp [z]; linarith
  have hrz : (p + cr) ^ cr ≤ z := by dsimp [z]; linarith
  have haz : (p + 2) ^ a ≤ z := by dsimp [z]; linarith
  have hbud := hbudget p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m₁, hm₁, hm₁bound, hlm₁, hresetm⟩ :=
    hreset F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T
      (fun i => (Real.exp_le_exp.mpr hbud.1).trans (hT i))
  obtain ⟨m₂, hm₂, hm₂bound, hm₁m₂, hproducts⟩ := hratprod F b ω hF v hv H z hH hz
    (hι.trans hpz) (hτ.trans hpz) (hHp.trans (Real.exp_le_exp.mpr hpz)) hb m₁ hm₁
    (hm₁bound.trans (Real.exp_le_exp.mpr hrz))
  refine ⟨m₂, hm₂, hm₂bound.trans (Real.exp_le_exp.mpr hbud.2.2), hlm₁.trans hm₁m₂, ?_⟩
  intro U vg hspan hvg σ w β hβ K hK g E R k hk hx
  dsimp only
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
    (fun i => weightedHomogeneousComponent v (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  intro El Pl Rl hlocal hPl hEl hE hRl hR
  obtain ⟨P₀, hP₀, hidentity⟩ := F.exists_actual_path_common_quotient_splitting
    b ω hF w v β hβ U K hK g E R k hx El Pl Rl hlocal
  obtain ⟨hprod, hmid, hEq, hRq, hslow, hgrid⟩ := hresetm
    (F.symbolPointwiseSubalgebra b ω hF v U) vg hspan
    (F.symbolPointwiseSubalgebra_basisGraded b ω hF v hv U) hvg k hk El Pl Rl
    (pull E) P₀ (pull R) hPl hP₀
    (congrArg (F.realSymbolGradeQuotientHom v k) hidentity) hEl hE hRl hR
  let A := F.truncateRealSymbol b ω hF v k ((pull E)⁻¹ * El)
  let D := F.truncateRealSymbol b ω hF v k (Rl * (pull R)⁻¹)
  have hslowdiff : F.SymbolSlowBound b ω hF v T
      (Real.exp ((p + C) ^ C)) ((pull E)⁻¹ * (El * A⁻¹)) := by
    have hinput : ∀ x ∈ [(pull E)⁻¹, El * A⁻¹],
        F.SymbolSlowBound b ω hF v T (Real.exp ((z + 2) ^ 1)) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · apply (F.symbolSlowBound_inv_iff b ω hF v T _ _).mpr
        exact F.symbolSlowBound_mono b ω hF v T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using haz.trans (by linarith : z ≤ z + 2)))
          _ hE
      · exact F.symbolSlowBound_mono b ω hF v T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using hrz.trans (by linarith : z ≤ z + 2)))
          _ hslow
    have h := hslowprod F b ω hF v hv H z hH hz (hι.trans hpz) (hτ.trans hpz)
      (hHp.trans (Real.exp_le_exp.mpr hpz)) hb T hTpos [(pull E)⁻¹, El * A⁻¹] (by simp) hinput
    simp only [List.prod_cons, List.prod_nil, mul_one] at h
    exact F.symbolSlowBound_mono b ω hF v T hTpos (Real.exp_le_exp.mpr hbud.2.1) _ h
  have hgriddiff : F.SymbolRationalGrid b ω hF v m₂ ((D⁻¹ * Rl) * (pull R)⁻¹) := by
    have hinput : ∀ x ∈ [D⁻¹ * Rl, (pull R)⁻¹], F.SymbolRationalGrid b ω hF v m₁ x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hgrid
      · exact F.symbolRationalGrid_inv b ω hF v m₁
          (F.symbolRationalGrid_mono b ω hF v hl hlm₁ _ hR)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts [D⁻¹ * Rl, (pull R)⁻¹] (by simp) hinput
  exact ⟨El * A⁻¹, A * Pl * D, D⁻¹ * Rl, hprod.trans hlocal, hmid, hEq.symm, hRq,
    F.symbolSlowBound_mono b ω hF v T hTpos (Real.exp_le_exp.mpr hbud.1) _ hslow,
    F.symbolRationalGrid_mono b ω hF v hm₁ hm₁m₂ _ hgrid, hslowdiff, hgriddiff⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistNativeApproximationBudget
namespace OAI

section

namespace Erdos3

noncomputable def allocatedModelTestLog (u p : ℝ) : ℝ := 2 * u + 5 * p + 12

noncomputable def allocatedModelUnitThreshold (u p K C : ℝ) : ℝ :=
  (Real.exp (-(u + 3)) / Real.exp p ^ 2) /
    max 1 (K * (2 * C) / Real.exp (-(u + 3)))

theorem allocatedModel_size_bounds {u p Q K C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) :
    2 / Real.exp (-Q) ≤ Real.exp (Q + 2) ∧
      1 + 4 * (K * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤
        Real.exp (2 * Q + 2 * u + 4 * p + 30) := by
  constructor
  · rw [Real.exp_neg, div_eq_mul_inv, inv_inv, Real.exp_add]
    nlinarith [Real.add_one_le_exp (2 : ℝ), Real.exp_pos Q]
  · let L := 2 * Q + 2 * u + 4 * p + 6
    have hL : 0 ≤ L := by dsimp only [L]; positivity
    have hlarge : 1 ≤ Real.exp L := Real.one_le_exp hL
    have hratio : 4 * (K * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤ 16 * Real.exp L := by
      calc
        _ ≤ 4 * (Real.exp p * (2 * Real.exp p)) ^ 2 /
            (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) := by gcongr
        _ = 16 * Real.exp L := by
          dsimp only [L]
          rw [Real.exp_neg, Real.exp_neg,
            show 2 * Q + 2 * u + 4 * p + 6 = Q + Q + ((u + 3) + (u + 3)) + ((p + p) + (p + p)) by ring]
          simp only [Real.exp_add]
          field_simp
          ring
    calc
      _ ≤ 17 * Real.exp L := by linarith
      _ ≤ Real.exp L * Real.exp 24 := by
        nlinarith [Real.add_one_le_exp (24 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [L]; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_native_approximation_with_budget
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ)
    {u p budget K C : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ budget)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ t, ‖signal t‖ ≤ 1) →
      (∀ t, t ∉ integerBox N → signal t = 0) →
      allocatedModelUnitThreshold u p K C ≤ sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) G) ∧
        Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun t => signal t.val)
            (fun t => star (W.eval N poly t.val) * G t)‖)
    {Ptail : ℝ} (hPtail : u + 2 * p + budget + 30 ≤ Ptail)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤
        6 * positiveProjectionAccuracy Ptail)
    (input : integerBox N → ℂ) (hinput : ∀ t, ‖input t‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
        (fun t : integerBox N => t.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (t : integerBox N) => W.eval N poly t.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
      sampledSliceSeminorm μ physical slices tests err ≤ Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * p + 30) := by
  obtain ⟨nterms, hnterms, Q, coeff, err, hQ, heq, hcoeff, herr, hterms⟩ :=
    exists_normalizedTwist_native_approximation N poly μ physical site hphysical slices tests
      w degree budget hK hC (Real.exp_pos p) (Real.exp_pos (-budget))
      (Real.exp_pos (-(u + 3))) hsize htests hdetect hexcess input hinput
  have hbounds := allocatedModel_size_bounds hu hp hbudget hK hC hKp hCp
  refine ⟨nterms, hnterms, Q, coeff, err, hQ, heq, hcoeff.trans hbounds.1,
    herr.trans ?_, hterms.trans hbounds.2⟩
  exact allocated_native_approximation_error hu hp hbudget hK (Real.exp_nonneg p)
    hKp le_rfl le_rfl hPtail le_rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankUnadaptedFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def rankVerticalSelectionBudget (p : ℝ) : ℝ := p + verticalDecompositionBudget (p + 1) + 1

theorem rankVerticalSelectionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    p + 1 ≤ rankVerticalSelectionBudget p ∧
      verticalDecompositionBudget (p + 1) ≤ rankVerticalSelectionBudget p := by
  have h := verticalDecompositionBudget_nonneg (show 0 ≤ p + 1 by linarith)
  unfold rankVerticalSelectionBudget
  constructor <;> linarith

namespace RationalFilteredNilmanifold.Niltest

open CircleFourier

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_biased_mode_restricting_frequency (T : D.Niltest (fun _ : σ => 1))
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (S : Submodule ℚ L) (hS : S ≤ D.filtration.layer s) (η : L →ₗ[ℚ] ℚ)
    (hchar : ∀ y ∈ S, ∀ t : ℝ, ∀ x,
      T.observable ((⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) • x) =
        character ((t * (η y : ℝ) : ℝ) : CircleFourier.Circle) * T.observable x)
    (Q : Finset (σ → ℤ)) (hQ : Q.Nonempty)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ Q, T.eval x‖) :
    ∃ (ξ : L →ₗ[ℚ] ℚ) (U : D.Niltest (fun _ : σ => 1)),
      U.ComplexityLE (rankVerticalSelectionBudget p) ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (ξ (D.basis i)) ≤ rankVerticalSelectionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) *
          U.observable x) ∧
      (∀ y ∈ S, ξ y = η y) ∧
      Real.exp (-rankVerticalSelectionBudget p) ≤ ‖𝔼 x ∈ Q, U.eval x‖ := by
  have hp1 : 0 ≤ p + 1 := by linarith
  have hρp : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div, Real.exp_neg]; field_simp
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  obtain ⟨ξ, U, hU, hOrbit, hheight, hvert, _, hpres, hc⟩ :=
    T.exists_correlating_vertical_mode_preserving_characters hp1
      (hT.mono (by linarith)) (Real.exp_pos (-p)) hρp hQ (fun _ => 1)
      (fun _ _ => by simp) (by rwa [norm_finiteCorrelation_one])
  rw [norm_finiteCorrelation_one] at hc
  have hthreshold : Real.exp (-rankVerticalSelectionBudget p) ≤
      Real.exp (-p) / (2 * Real.exp (verticalDecompositionBudget (p + 1))) := by
    calc
      _ = Real.exp (-p - 1) / Real.exp (verticalDecompositionBudget (p + 1)) := by
        rw [← Real.exp_sub]
        congr 1
        unfold rankVerticalSelectionBudget
        ring
      _ ≤ (Real.exp (-p) / 2) / Real.exp (verticalDecompositionBudget (p + 1)) :=
        div_le_div_of_nonneg_right (exp_sub_one_le_half_exp (-p)) (Real.exp_nonneg _)
      _ = _ := by ring
  have hfinal := hthreshold.trans hc
  have hne : ∃ x, U.observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, U.eval x = 0 := fun x => hzero _
    simp only [heval, Finset.expect_const_zero, norm_zero] at hfinal
    exact (not_le_of_gt (Real.exp_pos _)) hfinal
  refine ⟨ξ, U, hU.mono (rankVerticalSelectionBudget_bounds hp).1, hOrbit,
    fun i => (hheight i).trans (rankVerticalSelectionBudget_bounds hp).2, hvert, ?_, hfinal⟩
  intro y hy
  have heq := vertical_frequency_on_real_direction D.filtration D.realLattice ξ U.observable
    hvert hne y (hS hy) (η y : ℝ) (fun t x => hpres _ _ (hchar y hy t) x)
  exact_mod_cast heq

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_biased_factorization_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      rankVerticalSelectionBudget p ≤ (p + C) ^ C ∧
      (rankVerticalSelectionBudget p + c) ^ c ≤ (p + C) ^ C := by
  obtain ⟨a, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 1 + Polynomial.C a) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hq : rankVerticalSelectionBudget p ≤ p + (p + 1 + a) ^ a + 1 := by
    have h := hvertical (p + 1) (by linarith)
    unfold rankVerticalSelectionBudget
    linarith only [h]
  have hq0 : 0 ≤ rankVerticalSelectionBudget p :=
    (show 0 ≤ p + 1 by linarith).trans (rankVerticalSelectionBudget_bounds hp).1
  have hY : 0 ≤ p + (p + 1 + a) ^ a + 1 := by positivity
  have hZ : 0 ≤ (p + (p + 1 + a) ^ a + 1 + c) ^ c := by positivity
  have hpow : (rankVerticalSelectionBudget p + c) ^ c ≤
      (p + (p + 1 + a) ^ a + 1 + c) ^ c := by gcongr
  have hbound : p + (p + 1 + a) ^ a + 1 +
      (p + (p + 1 + a) ^ a + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hq, hZ, hbound], by linarith only [hpow, hY, hbound]⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_adapted_factorization_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      rankAdaptedNiltestBudget p ≤ (p + C) ^ C ∧
      (rankAdaptedNiltestBudget p + c) ^ c ≤ (p + C) ^ C ∧
      p + 1 ≤ (p + C) ^ C ∧ (p + 3) ^ 5 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := (X + 3) ^ 11 + X + 2
  let B := A + (A + 2) ^ 2
  let P := B + (B + Polynomial.C c) ^ c + (X + 3) ^ 5 + X + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ rankAdaptedNiltestBudget p := hp.trans (le_rankAdaptedNiltestBudget hp)
  have hpow : 0 ≤ (rankAdaptedNiltestBudget p + c) ^ c := by positivity
  have hinv : 0 ≤ (p + 3) ^ 5 := by positivity
  have htotal : rankAdaptedNiltestBudget p + (rankAdaptedNiltestBudget p + c) ^ c +
      (p + 3) ^ 5 + p + 1 ≤ (p + C) ^ C := by
    simpa [P, B, A, X, Polynomial.eval₂_pow, rankAdaptedNiltestBudget,
      rankAdaptedNiltestBase] using hbound p hp
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_biased_symbol_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      ∃ ξ : L →ₗ[ℚ] ℚ,
        (∀ x ∈ R.filtration.layer s r, ξ x = η x) ∧
        D.filtration.ControlledSymbolFactorization D.basis ω hF ξ (fun i => (lengths i : ℝ))
          (T.symbol D.basis ω hF) ((p + C) ^ C) := by
  obtain ⟨c, _, hstep⟩ := exists_translated_step_drop s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_biased_factorization_budget c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  have hS : R.filtration.layer s r ≤ D.filtration.layer s := by
    intro y hy
    have h := R.filtration.layer_le_associatedDegree s r hy
    rwa [R.associated] at h
  have hchar : ∀ y ∈ R.filtration.layer s r, ∀ t : ℝ, ∀ x,
      T.observable ((⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) • x) =
        character ((t * (η y : ℝ) : ℝ) : CircleFourier.Circle) * T.observable x := by
    intro y hy t x
    have hz : (⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) ∈ R.realSubgroup s r :=
      Submodule.tmul_mem_baseChange_of_mem t hy
    simpa only [realifyFunctional_tmul] using hvert _ hz x
  have hQ : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    have hi := hlengths i
    exact ⟨le_rfl, by omega⟩
  obtain ⟨ξ, U, hU, hOrbit, hheight, hUvert, hrestrict, hUbias⟩ :=
    T.exists_biased_mode_restricting_frequency hp hT _ hS η hchar _ hQ hbias
  let q := rankVerticalSelectionBudget p
  have hpq : p ≤ q := by
    have h := (rankVerticalSelectionBudget_bounds hp).1
    dsimp only [q]
    linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hfact := hstep D ω hF q hq (hσ.trans hpq) U hU ξ hheight hUvert origin lengths hlengths
    (fun i => (Real.exp_le_exp.mpr (hbudget p hp).2).trans (hlarge i)) hUbias
  have hsymbol : U.symbol D.basis ω hF = T.symbol D.basis ω hF := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom D.basis ω hF (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) hOrbit
  rw [hsymbol] at hfact
  exact ⟨ξ, hrestrict, NilpotentLieFiltration.ControlledSymbolFactorization.mono
    D.filtration D.basis ω hF hfact (hbudget p hp).2 (fun i => by exact_mod_cast hlengths i)⟩

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_biased_refiltration (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      R.ControlledRankBracketFactorization ω hF η (fun i => (lengths i : ℝ))
        (T.symbol D.basis ω hF) ((p + C) ^ C) := by
  obtain ⟨C, hC, hfactor⟩ := exists_rank_biased_symbol_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  obtain ⟨ξ, hrestrict, h⟩ := hfactor D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  exact R.controlledRankBracketFactorization_of_frequency_restriction ω hF ξ η _ _ _ h hrestrict

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_unadapted_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → R.ComplexityLE p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      ∃ F : R.AdaptedData,
        F.rank.ComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ (p + C) ^ C) ∧
        (∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + C) ^ C) ∧
        F.rank.ControlledRankBracketFactorization F.weight F.layers η (fun i => (lengths i : ℝ))
          (T.symbol F.basis F.weight F.layers) ((p + C) ^ C) := by
  obtain ⟨c, _, hfactor⟩ := exists_rank_biased_refiltration s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_adapted_factorization_budget c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R p hp hσ hR T hT η hvert origin lengths hlengths hlarge hbias
  obtain ⟨F, hFR, hforward, hback, S, horbit, hobs, hS⟩ := R.exists_adapted_niltest T hp hR hT
  let q := rankAdaptedNiltestBudget p
  have hpq : p ≤ q := le_rankAdaptedNiltestBudget hp
  have hq : 0 ≤ q := hp.trans hpq
  obtain ⟨hqC, hfactorC, hforwardC, hbackC⟩ := hbudget p hp
  have hvertS : ∀ z ∈ F.rank.realSubgroup s r, ∀ x, S.observable (z • x) =
      character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * S.observable x := by
    intro z hz x
    rw [hobs]
    exact hvert z hz x
  have heval (x : σ → ℤ) : S.eval x = T.eval x := by
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [hobs, horbit]
    rfl
  have hbiasS : Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, S.eval x‖ := by
    simp only [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
  have hfact := hfactor F.model F.rank F.weight F.layers q hq (hσ.trans hpq)
    S hS η hvertS origin lengths hlengths
    (fun i => (Real.exp_le_exp.mpr hfactorC).trans (hlarge i)) hbiasS
  have hsymbol : S.symbol F.basis F.weight F.layers = T.symbol F.basis F.weight F.layers := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom F.basis F.weight F.layers (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) horbit
  change F.rank.ControlledRankBracketFactorization F.weight F.layers η (fun i => (lengths i : ℝ))
    (S.symbol F.basis F.weight F.layers) ((q + c) ^ c) at hfact
  rw [hsymbol] at hfact
  refine ⟨F, hFR.mono F.rank hqC,
    (fun i j => (hforward i j).trans hforwardC),
    (fun j i => (hback j i).trans hbackC), ?_⟩
  exact RationalFilteredNilmanifold.DegreeRankStructure.ControlledRankBracketFactorization.mono
    F.rank F.weight F.layers hfact hfactorC (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

def rankIntervalInputBudget (c : ℕ) (p : ℝ) : ℝ :=
  (p + c) ^ c + raisedNiltestBudget p + p + 5

theorem rankIntervalInputBudget_bounds (c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    5 ≤ rankIntervalInputBudget c p ∧ p + 4 ≤ rankIntervalInputBudget c p ∧
      raisedNiltestBudget p ≤ rankIntervalInputBudget c p ∧
      (p + c) ^ c ≤ rankIntervalInputBudget c p := by
  have ha : 0 ≤ (p + c) ^ c := by positivity
  have hb : 0 ≤ raisedNiltestBudget p := by unfold raisedNiltestBudget; positivity
  unfold rankIntervalInputBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_rank_interval_product_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      productNiltestBudget (rankIntervalInputBudget c p) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C c) ^ c + (X + (X + 2) ^ 2 + 3) + X + 5
  let P := (U + 2) ^ 2 + U + (U + (U ^ 2 + U + 3) ^ 2) + U ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, U, X, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget,
    rankIntervalInputBudget, raisedNiltestBudget] using hbound p hp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

noncomputable def productRankLayerBasis (j k : Fin (s + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((R i).filtration.layer j.val k.val))) ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val) :=
  (Pi.basis (fun i => (R i).basis j k)).map
    (DegreeRankLieFiltration.piLayerEquiv (fun i => (R i).filtration) j.val k.val)

noncomputable def productRankLayerFinBasis (j k : Fin (s + 1)) :
    Basis (Fin (finrank ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val))) ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val) :=
  (productRankLayerBasis D R j k).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productRankLayerBasis D R j k)).symm)

noncomputable def piRank : (pi D).DegreeRankStructure r where
  filtration := DegreeRankLieFiltration.pi (fun i => (R i).filtration)
  associated := by
    rw [DegreeRankLieFiltration.pi_associatedDegree]
    exact congrArg NilpotentLieFiltration.pi (funext (fun i => (R i).associated))
  basis := productRankLayerFinBasis D R

theorem productRankLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p) (j k : Fin (s + 1))
    (a : Σ i, Fin (finrank ℚ ((R i).filtration.layer j.val k.val)))
    (b : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr
      ((productRankLayerBasis D R j k a).val) b) ≤ p := by
  classical
  rcases a with ⟨a, m⟩
  rcases b with ⟨b, n⟩
  simp only [productRankLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D b).basis.repr
    (((Pi.basis (fun i => (R i).basis j k)) ⟨a, m⟩ b).val) n) ≤ p
  rw [Pi.basis_apply]
  by_cases hab : a = b
  · subst b
    rw [Pi.single_eq_same]
    exact (hR a).2 j k m n
  · rw [Pi.single_eq_of_ne (Ne.symm hab)]
    simpa [rationalLogHeight] using hp

theorem piRank_complexity {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p) :
    (piRank D R).ComplexityLE ((p + 2) ^ 2) := by
  refine ⟨pi_geometry D hp hι (fun i => (hR i).1), ?_⟩
  intro j k a b
  change Fin (finrank ℚ
    ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val)) at a
  change rationalLogHeight ((productFinBasis D).repr
    ((productRankLayerFinBasis D R j k a).val) b) ≤ (p + 2) ^ 2
  rw [productFinBasis, Basis.repr_reindex_apply, productRankLayerFinBasis, Basis.reindex_apply]
  exact (productRankLayerBasis_logHeight D R hp hR j k _ _).trans (by nlinarith [sq_nonneg p])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) {G : NilpotentLieFiltration L s}

theorem orbitEquivOfEq_log (h : F = G) (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    (F.orbitEquivOfEq h w g).log = g.log := by
  subst G
  rfl

theorem orbitEquivOfEq_translate (h : F = G) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : F.PolynomialOrbit w) (a : σ → ℤ) :
    F.orbitEquivOfEq h w (g.translate hw a) = (F.orbitEquivOfEq h w g).translate hw a := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem orbitEquiv_log (w : σ → ℕ) (g : D.filtration.realification.PolynomialOrbit w) :
    (R.orbitEquiv w g).log = g.log :=
  D.filtration.realification.orbitEquivOfEq_log R.real_associated.symm w g

theorem orbitEquiv_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : D.filtration.realification.PolynomialOrbit w) (a : σ → ℤ) :
    R.orbitEquiv w (g.translate hw a) = (R.orbitEquiv w g).translate hw a :=
  D.filtration.realification.orbitEquivOfEq_translate R.real_associated.symm w hw g a

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

theorem productProjectionHom_mem_rank (i : ι) (k j : ℕ) (g : (pi D).RealGroup)
    (hg : g ∈ (piRank D R).realSubgroup k j) :
    productProjectionHom D i g ∈ (R i).realSubgroup k j := by
  apply baseChange_mem_of_mapsTo ((piRank D R).filtration.layer k j)
    ((R i).filtration.layer k j) (liePiEval i).toLinearMap _ hg
  intro x hx
  exact (DegreeRankLieFiltration.mem_pi_layer (fun i => (R i).filtration) k j x).mp hx i

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {w : σ → ℕ}

theorem productObservable_rank_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (hvert : ∀ i z, z ∈ (R i).realSubgroup s r → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (piRank D R).realSubgroup s r)
    (x : (pi D).Space) :
    productObservable D T (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        productObservable D T x := by
  have hchar :
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) =
        ∏ i, CircleFourier.character
          ((realifyFunctional (eta i) (productProjectionHom D i z).coord : ℝ) : CircleFourier.Circle) := by
    rw [realify_piFrequency]
    have hcoe (f : ι → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) =
        ∑ i, (f i : CircleFourier.Circle) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
    simp only [hcoe, CircleFourier.character_fintype_sum,
      productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  rw [hchar, productObservable, productObservable, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_smul]
  exact hvert i _ (productProjectionHom_mem_rank D R i s r z hz) _

variable [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem piNiltest_rank_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hvert : ∀ i z, z ∈ (R i).realSubgroup s r → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (piRank D R).realSubgroup s r)
    (x : (pi D).Space) :
    (piNiltest D T hp hι hT).observable (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        (piNiltest D T hp hι hT).observable x :=
  productObservable_rank_vertical D R T eta hvert z hz x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NativeDegreeRankFamily

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def fourPointFactors (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ) :
    Fin 4 → W.model.Niltest (fun _ : Unit => 1) :=
  ![(W.component out (a 0)).conjugate,
    (W.component out (a 1)).translate (fun _ => by decide) (fun _ => δ),
    W.component out (a 2),
    ((W.component out (a 3)).translate (fun _ => by decide) (fun _ => δ)).conjugate]

noncomputable def fourPointFrequencies : Fin 4 → (W.L →ₗ[ℚ] ℚ) :=
  ![-W.vertical.frequency, W.vertical.frequency, W.vertical.frequency, -W.vertical.frequency]

theorem fourPointFactors_complexity (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ : ℤ) (i : Fin 4) :
    (W.fourPointFactors out a δ i).ComplexityLE (p + 4) := by
  fin_cases i
  · exact W.component_complexity hp out (a 0)
  · exact W.component_complexity hp out (a 1)
  · exact W.component_complexity hp out (a 2)
  · exact W.component_complexity hp out (a 3)

theorem fourPointFactors_eval (out : Fin W.outputDim) (a : Fin 4 → A) (δ n : ℤ) :
    (∏ i, (W.fourPointFactors out a δ i).eval (fun _ => n)) =
      fourPointProduct (W.eval out (a 0)) (W.eval out (a 1))
        (W.eval out (a 2)) (W.eval out (a 3)) δ n := by
  have hshift : (fun _ : Unit => n) + (fun _ => δ) = (fun _ => n + δ) := rfl
  simp [fourPointFactors, Fin.prod_univ_succ, fourPointProduct, component_eval, hshift, mul_assoc]

theorem fourPointFactors_vertical (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ)
    (i : Fin 4) (z : W.model.RealGroup) (hz : z ∈ W.rank.realSubgroup s r)
    (x : W.model.Space) :
    (W.fourPointFactors out a δ i).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.fourPointFrequencies i) z.coord : ℝ) : CircleFourier.Circle) *
          (W.fourPointFactors out a δ i).observable x := by
  have h := W.vertical.vertical out z hz x
  have hn : star (W.vertical.observable out (z • x)) =
      CircleFourier.character
        ((realifyFunctional (-W.vertical.frequency) z.coord : ℝ) : CircleFourier.Circle) *
          star (W.vertical.observable out x) := by
    rw [h, star_mul, realifyFunctional_neg, AddCircle.coe_neg, CircleFourier.character_neg]
    exact mul_comm _ _
  fin_cases i
  · exact hn
  · exact h
  · exact h
  · exact hn

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 4 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 4 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 4 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 4 → W.L))]

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3.NativeDegreeRankFamily

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {κ A : Type*} {s r : ℕ} {p : ℝ} (W : NativeDegreeRankFamily s r A p)
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

noncomputable def horizontalCoefficient (α : Unit →₀ ℕ) (a : A) :
    ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) α) :=
  Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α
    (W.rank.orbitEquiv (fun _ => 1) (W.orbit a)))

theorem fourPointFactors_orbit (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ) (k : Fin 4) :
    (W.fourPointFactors out a δ k).orbit =
      ![W.orbit (a 0), (W.orbit (a 1)).translate (fun _ => Nat.zero_lt_one) (fun _ => δ),
        W.orbit (a 2), (W.orbit (a 3)).translate (fun _ => Nat.zero_lt_one) (fun _ => δ)] k := by
  fin_cases k <;> rfl

theorem fourPoint_horizontalCoefficient (out : Fin W.outputDim) (a : Fin 4 → A)
    (δ : ℤ) (α : Unit →₀ ℕ) (k : Fin 4) :
    Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α
      (W.rank.orbitEquiv (fun _ => 1) (W.fourPointFactors out a δ k).orbit)) =
        W.horizontalCoefficient hs c τ hG α (a k) := by
  rw [W.fourPointFactors_orbit]
  fin_cases k
  · rfl
  · have h := congrArg
      (fun g : W.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) =>
        W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α g)
      (W.rank.orbitEquiv_translate (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
        (W.orbit (a 1)) (fun _ => δ))
    exact congrArg Multiplicative.toAdd (h.trans
      (W.rank.filtration.nativeHorizontalCoefficientHom_translate hs c τ hG
        (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) α
        (W.rank.orbitEquiv (fun _ => 1) (W.orbit (a 1))) (fun _ => δ)))
  · rfl
  · have h := congrArg
      (fun g : W.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) =>
        W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α g)
      (W.rank.orbitEquiv_translate (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
        (W.orbit (a 3)) (fun _ => δ))
    exact congrArg Multiplicative.toAdd (h.trans
      (W.rank.filtration.nativeHorizontalCoefficientHom_translate hs c τ hG
        (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) α
        (W.rank.orbitEquiv (fun _ => 1) (W.orbit (a 3))) (fun _ => δ)))

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

def rankQuadrupleParameters {N : ℕ} (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![t.2.1, t.2.1 - t.1, t.2.2, t.2.2 - t.1]

namespace NativeRankInterval

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

noncomputable def productModels (i : Fin I.expansion.count) : ∀ k : Option (Fin 4),
    RationalFilteredNilmanifold (optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) s
      (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k) :=
  optionFactors ((I.expansion.model i).raiseStep (Nat.sub_le s 1)) (fun _ : Fin 4 => W.model)

noncomputable def productRanks (i : Fin I.expansion.count)
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r) :
    ∀ k, (I.productModels i k).DegreeRankStructure r
  | none => R₀
  | some _ => W.rank

noncomputable def productTests (i : Fin I.expansion.count) :
    ∀ k, (I.productModels i k).Niltest (fun _ : Unit => 1)
  | none => (I.expansion.test i).raiseStep (Nat.sub_le s 1)
  | some k => W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch) k

noncomputable def productFrequencies (i : Fin I.expansion.count) :
    ∀ k, optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => W.fourPointFrequencies k

theorem productTests_eval (i : Fin I.expansion.count) (n : ℤ) :
    (∏ k, (I.productTests i k).eval (fun _ => n)) =
      fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
        (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) := by
  rw [Fintype.prod_option]
  change ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) *
    (∏ k, (W.fourPointFactors out (rankQuadrupleParameters t)
      (cyclicBranchOffset t.1 branch) k).eval (fun _ => n)) = _
  rw [W.fourPointFactors_eval]
  exact mul_comm _ _

theorem productTests_vertical (hs : 1 ≤ s) (i : Fin I.expansion.count)
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r)
    (k : Option (Fin 4)) (z : (I.productModels i k).RealGroup)
    (hz : z ∈ (I.productRanks i R₀ k).realSubgroup s r) (x : (I.productModels i k).Space) :
    (I.productTests i k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (I.productFrequencies i k) z.coord : ℝ) : CircleFourier.Circle) *
          (I.productTests i k).observable x := by
  cases k with
  | none => exact (I.expansion.test i).raiseStep_rank_vertical (by omega) R₀ z hz x
  | some k =>
    exact W.fourPointFactors_vertical out (rankQuadrupleParameters t)
      (cyclicBranchOffset t.1 branch) k z hz x

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

def rankCoordinateTuple {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (t : ZMod N × ZMod N × ZMod N) : (Σ _ : Fin 4, ι) → ℝ :=
  fun j => β (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1)) j.2

theorem rankCoordinateTuple_first12 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (a b h : ZMod N) (i : ι) : rankCoordinateTuple β (b - h, b, a) ⟨0, i⟩ = β h i := by
  simp [rankCoordinateTuple, rankQuadrupleParameters]

theorem rankCoordinateTuple_first13 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (c d h : ZMod N) (i : ι) :
    rankCoordinateTuple β (c - d, h + (c - d), c) ⟨0, i⟩ = β h i := by
  simp [rankCoordinateTuple, rankQuadrupleParameters]

theorem rankCoordinateTuple_fixed12 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (a b h h₀ : ZMod N) (j : Σ _ : ({1, 2} : Finset (Fin 4)), ι) :
    rankCoordinateTuple β (b - h, b, a) ⟨j.1, j.2⟩ =
      rankCoordinateTuple β (b - h₀, b, a) ⟨j.1, j.2⟩ := by
  have hj := j.1.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj <;> simp [rankCoordinateTuple, rankQuadrupleParameters, hj]

theorem rankCoordinateTuple_fixed13 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (c d h h₀ : ZMod N) (j : Σ _ : ({1, 3} : Finset (Fin 4)), ι) :
    rankCoordinateTuple β (c - d, h + (c - d), c) ⟨j.1, j.2⟩ =
      rankCoordinateTuple β (c - d, h₀ + (c - d), c) ⟨j.1, j.2⟩ := by
  have hj := j.1.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj <;> simp [rankCoordinateTuple, rankQuadrupleParameters, hj]

theorem card_selected_four_le {ι : Type*} [Fintype ι] (K : Finset (Fin 4)) :
    Fintype.card (Σ _ : K, ι) ≤ Fintype.card (Σ _ : Fin 4, ι) := by
  let f : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  exact Sigma.ext (Subtype.ext (congrArg Sigma.fst h))
    (heq_of_eq (congrArg (fun z : Σ _ : Fin 4, ι => z.2) h))

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_product (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          letI : FiniteDimensional ℚ
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
            (productFinBasis (I.productModels i)).finiteDimensional_of_finite
          letI := moduleTopology ℝ (ℝ ⊗[ℚ]
            (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
          letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space (ℝ ⊗[ℚ]
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
            realification_moduleTopology_t2 (productFinBasis (I.productModels i))
          ∃ T : (pi (I.productModels i)).Niltest (fun _ : Unit => 1),
            T.ComplexityLE ((p + C) ^ C) ∧
            (piRank (I.productModels i) (I.productRanks i R₀)).ComplexityLE ((p + C) ^ C) ∧
            T.orbit = NilpotentLieFiltration.piRealOrbit (fun k => (I.productModels i k).filtration)
              (fun k => (I.productTests i k).orbit) ∧
            (∀ n, T.eval (fun _ => n) =
              fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
                (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
                  ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n)) ∧
            (∀ z ∈ (piRank (I.productModels i) (I.productRanks i R₀)).realSubgroup s r, ∀ x,
              T.observable (z • x) = CircleFourier.character
                ((realifyFunctional (piFrequency (I.productFrequencies i)) z.coord : ℝ) :
                  CircleFourier.Circle) * T.observable x) ∧
            Real.exp (-(2 * p)) ≤
              ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length), T.eval x‖ := by
  obtain ⟨c, _, hlower⟩ := exists_rank_interval_raised_lower_term s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_interval_product_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I
  obtain ⟨i, R₀, hR₀, hzero, hT₀, hcorr⟩ := hlower I
  let u := rankIntervalInputBudget c p
  obtain ⟨hu5, hup, huraise, hurank⟩ := rankIntervalInputBudget_bounds c hp
  have hu : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 5).trans hu5
  have hub : u ≤ productNiltestBudget u := by
    have hg := productNiltestBudget_geometry hu
    nlinarith [sq_nonneg u]
  have hcost : productNiltestBudget u ≤ (p + C) ^ C := hbudget p hp
  have hsmall : u ≤ (p + C) ^ C := hub.trans hcost
  have hb : 0 ≤ b := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hbu : b ≤ u := hbp.trans (by linarith)
  have hcard : (Fintype.card (Option (Fin 4)) : ℝ) ≤ u := by
    simpa using hu5
  have htests : ∀ k, (I.productTests i k).ComplexityLE u := by
    intro k
    cases k with
    | none => exact hT₀.mono huraise
    | some k => exact (W.fourPointFactors_complexity hb out (rankQuadrupleParameters t)
        (cyclicBranchOffset t.1 branch) k).mono (by linarith)
  have hranks : ∀ k, (I.productRanks i R₀ k).ComplexityLE u := by
    intro k
    cases k with
    | none => exact hR₀.mono R₀ hurank
    | some _ => exact W.complexity.mono W.rank hbu
  refine ⟨i, R₀, hR₀.mono R₀ (hurank.trans hsmall), hzero, ?_⟩
  let : FiniteDimensional ℚ
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
    (productFinBasis (I.productModels i)).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    realification_moduleTopology_t2 (productFinBasis (I.productModels i))
  let T := piNiltest (I.productModels i) (I.productTests i) hu hcard htests
  have heval (n : ℤ) : T.eval (fun _ => n) =
      fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
        (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) :=
    (piNiltest_eval (I.productModels i) (I.productTests i) hu hcard htests _).trans
      (I.productTests_eval i n)
  refine ⟨T, (piNiltest_complexity _ _ hu hcard htests).mono hcost,
    (piRank_complexity _ _ hu hcard hranks).mono (piRank (I.productModels i) (I.productRanks i R₀))
      ((productNiltestBudget_geometry hu).trans hcost), rfl, heval, ?_, ?_⟩
  · exact piNiltest_rank_vertical _ _ _ _ hu hcard htests (I.productTests_vertical hs i R₀)
  · rw [unitIntervalBox_expect]
    simpa only [heval, two_mul] using hcorr

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

noncomputable def productOrbit :
    (pi (I.productModels i)).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
  NilpotentLieFiltration.piRealOrbit (fun k => (I.productModels i k).filtration)
    (fun k => (I.productTests i k).orbit)

noncomputable def productSymbol {κ : Type*}
    (e : Basis κ ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) (ω : κ → ℕ)
    (hF : ∀ j, (pi (I.productModels i)).filtration.layer j =
      Submodule.span ℚ (e '' {a | j ≤ ω a})) :
    (pi (I.productModels i)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1) :=
  (pi (I.productModels i)).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
    ⟨⟨(I.productOrbit i).log, (I.productOrbit i).property⟩⟩

variable [TopologicalSpace (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [T2Space (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]

theorem productSymbol_eq {κ : Type*}
    (e : Basis κ ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) (ω : κ → ℕ)
    (hF : ∀ j, (pi (I.productModels i)).filtration.layer j =
      Submodule.span ℚ (e '' {a | j ≤ ω a}))
    (T : (pi (I.productModels i)).Niltest (fun _ : Unit => 1)) (hT : T.orbit = I.productOrbit i) :
    T.symbol e ω hF = I.productSymbol i e ω hF := by
  unfold RationalFilteredNilmanifold.Niltest.symbol productSymbol
  apply congrArg ((pi (I.productModels i)).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1))
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : (pi (I.productModels i)).filtration.realification.PolynomialOrbit
    (fun _ : Unit => 1) => o.log) hT

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

def rankProjection :
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) →ₗ⁅ℚ⁆
      (Fin 4 → W.L) :=
  liePiMap (fun k : Fin 4 => liePiEval (R := ℚ)
    (M := optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L))
    (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)))

theorem rankProjection_frequency
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :
    piFrequency (I.productFrequencies i) x =
      W.vertical.frequency (I.rankProjection i x 0) + W.vertical.frequency (I.rankProjection i x 1) -
        W.vertical.frequency (I.rankProjection i x 2) - W.vertical.frequency (I.rankProjection i x 3) := by
  rw [piFrequency_apply, Fintype.sum_option]
  simp only [Fin.sum_univ_succ]
  change 0 + (-W.vertical.frequency (x (some 0)) +
    (W.vertical.frequency (x (some 1)) + (W.vertical.frequency (x (some 2)) +
      (-W.vertical.frequency (x (some 3)) + 0)))) =
    W.vertical.frequency (x (some 1)) + W.vertical.frequency (x (some 2)) -
      W.vertical.frequency (x (some 0)) - W.vertical.frequency (x (some 3))
  ring

theorem rankProjection_mem_layer (d : ℕ)
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (hx : x ∈ (pi (I.productModels i)).filtration.layer d) (k : Fin 4) :
    I.rankProjection i x k ∈ W.rank.filtration.layer d 1 := by
  have h := (NilpotentLieFiltration.mem_pi_layer (fun j => (I.productModels i j).filtration) d x).mp hx
    (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))
  change I.rankProjection i x k ∈ W.model.filtration.layer d at h
  rw [← W.rank.associated] at h
  change I.rankProjection i x k ∈ W.rank.filtration.layer d 0 at h
  rwa [W.rank.filtration.rank_zero_eq_one] at h

theorem rankProjection_mem_refiltered
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded) (d : ℕ)
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (hx : x ∈ (pi (I.productModels i)).filtration.gradedRefiltrationLayer U d) (k : Fin 4) :
    I.rankProjection i x k ∈ W.rank.filtration.layer d 1 :=
  I.rankProjection_mem_layer i d x
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer_le U d hx) k

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          ∃ F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData,
            F.rank.ComplexityLE ((p + C) ^ C) ∧
            (∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤
              (p + C) ^ C) ∧
            (∀ k j, rationalLogHeight (F.basis.repr ((pi (I.productModels i)).basis k) j) ≤
              (p + C) ^ C) ∧
            F.rank.ControlledRankBracketFactorization F.weight F.layers
              (piFrequency (I.productFrequencies i)) (fun _ : Unit => (I.length : ℝ))
              (I.productSymbol i F.basis F.weight F.layers) ((p + C) ^ C) := by
  obtain ⟨a, _, hproduct⟩ := exists_rank_interval_product s hs
  obtain ⟨c, _, hfactor⟩ := exists_rank_unadapted_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a + 2 * X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  let u := (p + a) ^ a + 2 * p + 1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hQu : (p + a) ^ a ≤ u := by dsimp [u]; linarith
  have h2pu : 2 * p ≤ u := by dsimp [u]; linarith
  have hone : 1 ≤ u := by dsimp [u]; linarith
  have hsum : u + (u + c) ^ c ≤ (p + C) ^ C := by
    simpa [U, X, u, Polynomial.eval₂_pow] using hbudget p hp
  have hfactor0 : 0 ≤ (u + c) ^ c := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hfactorC : (u + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨i, R₀, hR₀, hzero, htest⟩ := hproduct hp hbp I
  let : FiniteDimensional ℚ
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
    (productFinBasis (I.productModels i)).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    realification_moduleTopology_t2 (productFinBasis (I.productModels i))
  obtain ⟨T, hT, hR, horbit, _, hvert, hbias⟩ := htest
  have hbiasu : Real.exp (-u) ≤
      ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length), T.eval x‖ :=
    (Real.exp_le_exp.mpr (neg_le_neg h2pu)).trans hbias
  obtain ⟨F, hFR, hforward, hback, hF⟩ := hfactor (pi (I.productModels i))
    (piRank (I.productModels i) (I.productRanks i R₀)) u hu (by simpa using hone)
    (hR.mono _ hQu) T (hT.mono hQu) (piFrequency (I.productFrequencies i)) hvert
    (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length) (fun _ => I.length_pos)
    (fun _ => (Real.exp_le_exp.mpr hfactorC).trans hlarge) hbiasu
  have hsymbol := I.productSymbol_eq i F.basis F.weight F.layers T horbit
  rw [hsymbol] at hF
  refine ⟨i, R₀, hR₀.mono R₀ (hQu.trans huC), hzero, F, hFR.mono F.rank hfactorC,
    (fun j k => (hforward j k).trans hfactorC),
    (fun k j => (hback k j).trans hfactorC), ?_⟩
  exact DegreeRankStructure.ControlledRankBracketFactorization.mono F.rank F.weight F.layers
    hF hfactorC (fun _ => by exact_mod_cast I.length_pos)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realHorizontalMap :
    (F.layer d 1).baseChange ℝ →ₗ[ℝ] ℝ ⊗[ℚ] F.HigherHorizontal d :=
  ((F.higherHorizontalMk d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer d 1)).symm.toLinearMap

@[simp] theorem realHorizontalMap_baseChange (v : ℝ ⊗[ℚ] F.layer d 1) :
    F.realHorizontalMap d (realificationSubmoduleEquiv (F.layer d 1) v) =
      (F.higherHorizontalMk d).baseChange ℝ v := by
  exact congrArg ((F.higherHorizontalMk d).baseChange ℝ)
    ((realificationSubmoduleEquiv (F.layer d 1)).symm_apply_apply v)

theorem realHigherHorizontalCoordinates_map (x : (F.layer d 1).baseChange ℝ) :
    F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d x) =
      realRationalCoordinateEquiv ((F.ambientHorizontalCoordinates d f).baseChange ℝ x.val) := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective x
  rw [F.realHorizontalMap_baseChange]
  simp only [realificationSubmoduleEquiv_coe]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realHigherHorizontalCoordinates_mem (x : ℝ ⊗[ℚ] F.HigherHorizontal d) :
    F.realHigherHorizontalCoordinates d f x ∈
      realRationalCoordinateSpan ((F.layer d 1).map (F.ambientHorizontalCoordinates d f)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    obtain ⟨v, rfl⟩ := F.higherHorizontalMk_surjective d x
    exact ⟨a ⊗ₜ[ℚ] F.ambientHorizontalCoordinates d f v.val,
      Submodule.tmul_mem_baseChange_of_mem a ⟨v.val, v.property, rfl⟩, rfl⟩
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

theorem exists_controlled_horizontal_lifts
    {μ κ σ : Type*} [Fintype μ] [Fintype κ]
    (b : Basis μ ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = F.layer d 1)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hfH : ∀ j i, RationalHeightLE (F.ambientHorizontalCoordinates d f (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x y z : ℝ ⊗[ℚ] F.HigherHorizontal d)
        (a q : ι → ℝ), F.realHigherHorizontalCoordinates d f (x - y - z) = a + q →
        ‖a‖ ≤ Real.exp p / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : (F.layer d 1).baseChange ℝ,
          F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d E) = a ∧
          F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d Q) = q ∧
          x - y - F.realHorizontalMap d E - F.realHorizontalMap d Q = z ∧
          ‖(b.baseChange ℝ).equivFun E.val‖ ≤
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid m := by
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_controlled_coordinate_lifts b (F.layer d 1) v hv
    (F.ambientHorizontalCoordinates d f) hH hl hvH hfH hp hμ hι hκ hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x y z a q heq ha hq
  have hsum := F.realHigherHorizontalCoordinates_mem d f (x - y - z)
  rw [heq] at hsum
  obtain ⟨E, Q, hE, hQ, hEa, hQq, hslow, hgrid⟩ := hsolve α hα a q hsum ha hq
  let E' : (F.layer d 1).baseChange ℝ := ⟨E, hE⟩
  let Q' : (F.layer d 1).baseChange ℝ := ⟨Q, hQ⟩
  have hEa' : F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d E') = a :=
    (F.realHigherHorizontalCoordinates_map d f E').trans hEa
  have hQq' : F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d Q') = q :=
    (F.realHigherHorizontalCoordinates_map d f Q').trans hQq
  refine ⟨E', Q', hEa', hQq', ?_, hslow, hgrid⟩
  apply F.realHigherHorizontalCoordinates_injective d f
  simp only [map_sub] at heq ⊢
  rw [hEa', hQq']
  linear_combination heq

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_firstProjection_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (J : Submodule ℚ (Fin 4 → V)) {x : ℝ ⊗[ℚ] (Fin 4 → V)}
    (hx : x ∈ J.baseChange ℝ) :
    (LinearMap.proj (0 : Fin 4)).baseChange ℝ x ∈ (fourFirstProjection J).baseChange ℝ := by
  rw [fourFirstProjection, realification_map]
  exact ⟨x, hx, rfl⟩

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

noncomputable def realFourLayerComponent (k : Fin 4) :
    (F.fourHorizontalLayer d).baseChange ℝ →ₗ[ℝ] (F.layer d 1).baseChange ℝ :=
  (((LinearMap.proj k).baseChange ℝ).comp ((F.fourHorizontalLayer d).baseChange ℝ).subtype).codRestrict
    ((F.layer d 1).baseChange ℝ) (fun x => baseChange_mem_of_mapsTo
      (F.fourHorizontalLayer d) (F.layer d 1) (LinearMap.proj k)
      (fun v hv => (F.mem_fourHorizontalLayer d v).mp hv k) x.property)

@[simp] theorem realFourLayerComponent_coe (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    (F.realFourLayerComponent d k x).val = (LinearMap.proj k).baseChange ℝ x.val := rfl

theorem realFourLayerComponent_horizontal (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    (LinearMap.proj k).baseChange ℝ (F.realFourHorizontalMap d x) =
      F.realHorizontalMap d (F.realFourLayerComponent d k x) := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.fourHorizontalLayer d)).surjective x
  rw [F.realFourHorizontalMap_baseChange]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    let u : F.layer d 1 := ⟨v.val k, (F.mem_fourHorizontalLayer d v.val).mp v.property k⟩
    have heq : F.realFourLayerComponent d k
        (realificationSubmoduleEquiv (F.fourHorizontalLayer d) (a ⊗ₜ[ℚ] v)) =
        realificationSubmoduleEquiv (F.layer d 1) (a ⊗ₜ[ℚ] u) := by
      apply Subtype.ext
      rfl
    rw [heq, F.realHorizontalMap_baseChange]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourLayerComponent_norm_bound {ι : Type*} [Fintype ι] (b : Basis ι ℚ L)
    (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, |((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x.val j| ≤ B) :
    ‖(b.baseChange ℝ).equivFun (F.realFourLayerComponent d k x).val‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x.val) i| ≤ B
  rw [real_pi_projection_coordinates]
  exact hx ⟨k, i⟩

theorem realFourLayerComponent_grid {ι : Type*} (b : Basis ι ℚ L)
    (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) (l : ℕ)
    (hx : (fun j => ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x.val j) ∈ realDenominatorGrid l) :
    (fun i => (b.baseChange ℝ).repr (F.realFourLayerComponent d k x).val i) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => z ⟨k, i⟩, ?_⟩
  funext i
  exact (congrFun hz ⟨k, i⟩).trans (congrArg (fun a : ℝ => (l : ℝ) * a)
    (real_pi_projection_coordinates b x.val k i).symm)

end DegreeRankLieFiltration
end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realHorizontalMap_surjective (d : ℕ) :
    Function.Surjective (F.realHorizontalMap d) := by
  intro x
  obtain ⟨v, hv⟩ := LinearMap.baseChange_surjective ℝ (F.higherHorizontalMk_surjective d) x
  exact ⟨realificationSubmoduleEquiv (F.layer d 1) v,
    (F.realHorizontalMap_baseChange d v).trans hv⟩

theorem realHorizontalMap_ambient (d : ℕ) (x : (F.layer d 1).baseChange ℝ) :
    (F.higherHorizontalAmbient d).baseChange ℝ (F.realHorizontalMap d x) =
      (F.layer d 2).mkQ.baseChange ℝ x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective x
  rw [F.realHorizontalMap_baseChange]
  simp only [realificationSubmoduleEquiv_coe]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem realHorizontalMap_eq (d : ℕ) (x y : (F.layer d 1).baseChange ℝ) :
    F.realHorizontalMap d x = F.realHorizontalMap d y ↔
      x.val - y.val ∈ (F.layer d 2).baseChange ℝ := by
  rw [← realification_mkQ_eq_zero_iff, map_sub, sub_eq_zero]
  constructor
  · intro h
    rw [← F.realHorizontalMap_ambient d x, ← F.realHorizontalMap_ambient d y, h]
  · intro h
    apply F.real_higherHorizontalAmbient_injective d
    rwa [F.realHorizontalMap_ambient, F.realHorizontalMap_ambient]

noncomputable def realHorizontalRepresentative (d : ℕ)
    (x : ℝ ⊗[ℚ] F.HigherHorizontal d) : (F.layer d 1).baseChange ℝ := by
  classical
  exact if x = 0 then 0 else Classical.choose (F.realHorizontalMap_surjective d x)

@[simp] theorem realHorizontalRepresentative_zero (d : ℕ) :
    F.realHorizontalRepresentative d 0 = 0 := by
  classical
  simp only [realHorizontalRepresentative, ↓reduceIte]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankLayerCoefficient_tensor_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.layer (Finsupp.weight w α) 1).subtype.baseChange ℝ
        ((F.rankLayerCoefficient w α).baseChange ℝ x) =
      coefficients (F.associatedDegree.realAdaptedPolynomialMap w x) α := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
      F.rankLayerCoefficient_coe, F.associatedDegree.realAdaptedPolynomialMap_coefficient_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem rankLayerCoefficient_tensor_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.higherHorizontalMk (Finsupp.weight w α)).baseChange ℝ
        ((F.rankLayerCoefficient w α).baseChange ℝ x) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem nativeHorizontalCoefficientHom_eq_realHorizontalMap (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (v : (F.layer (Finsupp.weight w α) 1).baseChange ℝ)
    (hv : v.val = coefficients g.log α) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      F.realHorizontalMap (Finsupp.weight w α) v := by
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  have heq : v = realificationSubmoduleEquiv (F.layer (Finsupp.weight w α) 1)
      ((F.rankLayerCoefficient w α).baseChange ℝ x) := by
    apply Subtype.ext
    rw [realificationSubmoduleEquiv_coe, F.rankLayerCoefficient_tensor_coe, hv, hlog]
  rw [F.nativeHorizontalCoefficientHom_tensor hs b ω hF w α g x hlog, heq,
    F.realHorizontalMap_baseChange, F.rankLayerCoefficient_tensor_horizontal]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

def horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d)) : Submodule ℚ L :=
  (U.comap (F.higherHorizontalMk d)).map (F.layer d 1).subtype

theorem horizontalPreimage_le (U : Submodule ℚ (F.HigherHorizontal d)) :
    F.horizontalPreimage d U ≤ F.layer d 1 := by
  rintro x ⟨v, _, rfl⟩
  exact v.property

theorem horizontalPreimage_mono {U V : Submodule ℚ (F.HigherHorizontal d)} (h : U ≤ V) :
    F.horizontalPreimage d U ≤ F.horizontalPreimage d V :=
  Submodule.map_mono (Submodule.comap_mono h)

theorem mem_horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d))
    (v : F.layer d 1) :
    v.val ∈ F.horizontalPreimage d U ↔ F.higherHorizontalMk d v ∈ U := by
  constructor
  · rintro ⟨w, hw, h⟩
    have he : w = v := Subtype.ext h
    exact he ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem horizontalPreimage_coordinates {ι : Type*} [Fintype ι]
    (f : Basis ι ℚ (L ⧸ F.layer d 2)) (U : Submodule ℚ (F.HigherHorizontal d)) :
    F.horizontalPreimage d U = F.layer d 1 ⊓
      (U.map (F.higherHorizontalCoordinates d f)).comap (F.ambientHorizontalCoordinates d f) := by
  ext x
  constructor
  · intro hx
    have hxl := F.horizontalPreimage_le d U hx
    exact ⟨hxl, ⟨F.higherHorizontalMk d ⟨x, hxl⟩,
      (F.mem_horizontalPreimage d U ⟨x, hxl⟩).mp hx, rfl⟩⟩
  · rintro ⟨hxl, y, hy, he⟩
    apply (F.mem_horizontalPreimage d U ⟨x, hxl⟩).mpr
    have he' : y = F.higherHorizontalMk d ⟨x, hxl⟩ :=
      F.higherHorizontalCoordinates_injective d f he
    exact he' ▸ hy

theorem mem_real_horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d))
    (v : (F.layer d 1).baseChange ℝ) :
    v.val ∈ (F.horizontalPreimage d U).baseChange ℝ ↔
      F.realHorizontalMap d v ∈ U.baseChange ℝ := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective v
  rw [F.realHorizontalMap_baseChange, realificationSubmoduleEquiv_coe,
    horizontalPreimage, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := realification_subtype_injective (F.layer d 1) he
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem native_coefficient_mem_horizontalPreimage {σ ι : Type*} (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (U : Submodule ℚ (F.HigherHorizontal (Finsupp.weight w α))) :
    coefficients g.log α ∈ (F.horizontalPreimage (Finsupp.weight w α) U).baseChange ℝ ↔
      Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) ∈
        U.baseChange ℝ := by
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  let v := realificationSubmoduleEquiv (F.layer (Finsupp.weight w α) 1)
    ((F.rankLayerCoefficient w α).baseChange ℝ x)
  have hv : v.val = coefficients g.log α := by
    rw [hlog]
    exact F.rankLayerCoefficient_tensor_coe w α x
  rw [F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α g v hv,
    ← hv, F.mem_real_horizontalPreimage]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem polynomialOrbit_coefficient_mem_rank_one (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    coefficients g.log α ∈ (F.layer (Finsupp.weight w α) 1).baseChange ℝ := by
  have h := (F.associatedDegree.realification.adapted_iff_coefficients w g.log).mp g.adapted α
  change coefficients g.log α ∈ (F.layer (Finsupp.weight w α) 0).baseChange ℝ at h
  rwa [F.rank_zero_eq_one] at h

theorem polynomialOrbit_log_mul_mod_rank_two (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (F.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  let x : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients g.log α, F.polynomialOrbit_coefficient_mem_rank_one w α g⟩
  let y : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients h.log α, F.polynomialOrbit_coefficient_mem_rank_one w α h⟩
  let z : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients (g * h).log α, F.polynomialOrbit_coefficient_mem_rank_one w α (g * h)⟩
  apply (F.realHorizontalMap_eq (Finsupp.weight w α) z (x + y)).mp
  rw [← F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α (g * h) z rfl,
    map_mul]
  change Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) +
      Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α h) = _
  rw [F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α g x rfl,
    F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α h y rfl, map_add]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)

theorem orbit_log_mul_mod_rank_two (hs : 1 ≤ s) (c : Basis ι ℚ L) (τ : ι → ℕ)
    (hF : ∀ j, T.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (g h : E.filtration.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  have hp := T.filtration.polynomialOrbit_log_mul_mod_rank_two hs c τ hF w α
    (T.orbitEquiv w g) (T.orbitEquiv w h)
  have hprod : ((T.orbitEquiv w g) * (T.orbitEquiv w h)).log = (g * h).log :=
    (congrArg (fun z => z.log) (map_mul (T.orbitEquiv w) g h).symm).trans
      (T.orbitEquiv_log w (g * h))
  have heq := congrArg₂ (fun x y => x - y) (congrArg (fun z => coefficients z α) hprod)
    (congrArg₂ (fun x y => x + y)
      (congrArg (fun z => coefficients z α) (T.orbitEquiv_log w g))
      (congrArg (fun z => coefficients z α) (T.orbitEquiv_log w h)))
  exact (congrArg (fun z => z ∈ (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ) heq).mp hp

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankProductOrbitCoefficients
namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem rankProjection_coefficient (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        ((I.rankProjection i).toLinearMap.baseChange ℝ (coefficients (I.productOrbit i).log α)) =
      coefficients ((W.fourPointFactors out (rankQuadrupleParameters t)
        (cyclicBranchOffset t.1 branch) ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit).log α := by
  change realificationLieHom (liePiEval k)
    (realificationLieHom (I.rankProjection i) (coefficients (I.productOrbit i).log α)) = _
  have h := realification_liePiEval_liePiMap (M := fun _ : Fin 4 => W.L)
    (fun j : Fin 4 => (liePiEval (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j)) :
      (∀ a : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) a) →ₗ⁅ℚ⁆ W.L))
    (coefficients (I.productOrbit i).log α) k
  apply h.trans
  exact NilpotentLieFiltration.piRealOrbit_coefficient
    (fun j => (I.productModels i j).filtration) (fun j => (I.productTests i j).orbit)
    α (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))

theorem rankProjection_component_log (k : Fin 4) :
    VectorPolynomial.map
        ((realificationLieHom ((liePiEval k).comp (I.rankProjection i))).toLinearMap.restrictScalars ℚ)
        (I.productOrbit i).log =
      (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
        ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit.log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  change ((LinearMap.proj k).comp (I.rankProjection i).toLinearMap).baseChange ℝ
    (coefficients (I.productOrbit i).log α) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact I.rankProjection_coefficient i α k

end Erdos3.NativeRankInterval

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realifyFunctional_lieTreeEval_rational (η : L →ₗ[ℚ] ℚ) (v : I → L) (a : FreeMagma I) :
    realifyFunctional η (lieTreeEval (fun i => rationalLieInclusion (v i)) a) =
      (η (lieTreeEval v a) : ℝ) := by
  rw [lieTreeEval_hom rationalLieInclusion v a]
  simp only [rationalLieInclusion_apply, realifyFunctional_tmul, one_mul]

theorem rational_lieTree_kernel_of_real (A : I → Submodule ℚ L)
    (η : L →ₗ[ℚ] ℚ) (a : FreeMagma I)
    (hker : ∀ z : I → ℝ ⊗[ℚ] L, (∀ i, z i ∈ (A i).baseChange ℝ) →
      realifyFunctional η (lieTreeEval z a) = 0)
    (v : I → L) (hv : ∀ i, v i ∈ A i) : η (lieTreeEval v a) = 0 := by
  have h := hker (fun i => rationalLieInclusion (v i))
    (fun i => Submodule.tmul_mem_baseChange_of_mem (1 : ℝ) (hv i))
  rw [realifyFunctional_lieTreeEval_rational] at h
  exact_mod_cast h

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

noncomputable def refilteredHorizontalImage (d : ℕ) :
    Submodule ℚ (Fin 4 → W.rank.filtration.HigherHorizontal d) :=
  W.rank.filtration.layerHorizontalImage
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) d

theorem refilteredHorizontalImage_frequency {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, Fin 4 → W.rank.filtration.HigherHorizontal (d j))
    (hv : ∀ j, v j ∈ I.refilteredHorizontalImage i U (d j)) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 0)) +
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 1)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 2)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 3)) = 0 := by
  apply W.rank.filtration.layerHorizontalImage_frequency
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) W.vertical.frequency d a hd hr ?_ v hv
  intro u hu
  rw [← I.rankProjection_frequency i]
  exact rational_lieTree_kernel_of_real
    (fun j => (pi (I.productModels i)).filtration.gradedRefiltrationLayer U (d j))
    (piFrequency (I.productFrequencies i)) a hker u hu

theorem refiltered_sunflower_bracket {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, W.rank.filtration.HigherHorizontal (d j))
    (hv : ∀ j, v j ∈ fourFirstProjection (I.refilteredHorizontalImage i U (d j)))
    (j k : J) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d j)))
    (hvk : v k ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d k))) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a) (W.rank.filtration.horizontalTreeValue d a)
    (fun u j hj hu => W.rank.filtration.horizontalTreeValue_zero_of_leaf d a u (i := j) hj hu)
    W.vertical.frequency (map_zero _) (fun j => I.refilteredHorizontalImage i U (d j))
    (I.refilteredHorizontalImage_frequency i U d a hd hr hker) v hv j k hjk hj hk hvj hvk

def SunflowerKernel : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ) (a : FreeMagma (Fin n)),
    lieTreeWeight d a = s → a.length = r →
    ∀ v : ∀ j, W.rank.filtration.HigherHorizontal (d j),
      (∀ j, v j ∈ fourFirstProjection (I.refilteredHorizontalImage i U (d j))) →
      ∀ j k, j ≠ k → j ∈ lieTreeSupport a → k ∈ lieTreeSupport a →
      v j ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d j)) →
      v k ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d k)) →
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a v) = 0

def BracketKernel : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ) (a : FreeMagma (Fin n)),
    lieTreeWeight d a = s → a.length = r →
    ∀ z : Fin n → ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
    (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
    realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0

theorem sunflowerKernel_of_real (hker : I.BracketKernel i U) :
    I.SunflowerKernel i U := by
  intro n d a hd hr v hv j k hjk hj hk hvj hvk
  exact I.refiltered_sunflower_bracket i U d a hd hr (hker n d a hd hr) v hv j k hjk hj hk hvj hvk

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

noncomputable def refilteredProjectionImage (d : ℕ) : Submodule ℚ (Fin 4 → W.L) :=
  ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U d).map (I.rankProjection i).toLinearMap

theorem refilteredHorizontalImage_eq (d : ℕ) :
    I.refilteredHorizontalImage i U d =
      W.rank.filtration.horizontalImageOfSubmodule (I.refilteredProjectionImage i U d) d :=
  W.rank.filtration.layerHorizontalImage_eq_of_submodule
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) d

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_sunflower (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          ∃ F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData,
            F.rank.ComplexityLE ((p + C) ^ C) ∧
            (∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤
              (p + C) ^ C) ∧
            (∀ k j, rationalLogHeight (F.basis.repr ((pi (I.productModels i)).basis k) j) ≤
              (p + C) ^ C) ∧
            ∃ (l : ℕ) (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
              (v : Fin (finrank ℚ (∀ k : Option (Fin 4),
                optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) →
                (pi (I.productModels i)).filtration.AssociatedGraded),
              0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
              BasisGradedSubmodule
                ((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers)
                F.weight U.toSubmodule ∧
              (∀ j k, rationalLogHeight
                (((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers).repr
                  (v j) k) ≤ (p + C) ^ C) ∧
              I.BracketKernel i U ∧ I.SunflowerKernel i U ∧
              (pi (I.productModels i)).filtration.SymbolFactorizationIn F.basis F.weight F.layers
                (fun _ : Unit => (I.length : ℝ)) (I.productSymbol i F.basis F.weight F.layers)
                ((p + C) ^ C) l U := by
  obtain ⟨C, hC, hfactor⟩ := exists_rank_interval_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  obtain ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, hfact⟩ := hfactor hp hbp I hlarge
  obtain ⟨l, U, v, hl, hlp, hv, hU, hheight, hker, hinside⟩ :=
    DegreeRankStructure.ControlledRankBracketFactorization.exists_in F.rank F.weight F.layers hfact
  exact ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, l, U, v, hl, hlp, hv, hU, hheight,
    hker, I.sunflowerKernel_of_real i U hker, hinside⟩

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

noncomputable def fourRankBasis {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p) :
    Basis (Σ _ : Fin 4, Fin W.dim) ℚ (Fin 4 → W.L) :=
  Pi.basis (fun _ : Fin 4 => W.model.basis)

end NativeDegreeRankFamily

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem rankProjection_coordinates
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (j : Σ _ : Fin 4, Fin W.dim) :
    W.fourRankBasis.repr (I.rankProjection i x) j =
      (pi (I.productModels i)).basis.repr x
        ((Fintype.equivFin (Σ k : Option (Fin 4),
          Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
          ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩) := by
  change (Pi.basis (fun _ : Fin 4 => W.model.basis)).repr (I.rankProjection i x) j = _
  rw [Pi.basis_repr]
  let k : Σ a : Option (Fin 4), Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) a) :=
    ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩
  have hk := (Fintype.equivFin _).symm_apply_apply k
  have h := productFinBasis_repr (I.productModels i) x ((Fintype.equivFin _) k)
  have heq := congrArg (fun z : Σ a : Option (Fin 4),
      Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) a) =>
    (I.productModels i z.1).basis.repr (x z.1) z.2) hk
  exact (h.trans heq).symm

theorem rankProjection_coordinates_logHeight
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    {P : ℝ} (hx : ∀ j, rationalLogHeight ((pi (I.productModels i)).basis.repr x j) ≤ P)
    (j : Σ _ : Fin 4, Fin W.dim) :
    rationalLogHeight (W.fourRankBasis.repr (I.rankProjection i x) j) ≤ P := by
  rw [I.rankProjection_coordinates i x j]
  exact hx _

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem refilteredProjectionImage_mem_candidates
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r)
    (F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData)
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
    (v : Fin (finrank ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) →
      (pi (I.productModels i)).filtration.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {P : ℝ} (hP : 0 ≤ P) (hF : F.rank.ComplexityLE P)
    (hforward : ∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤ P)
    (hv : ∀ j k, rationalLogHeight
      (((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers).repr
        (v j) k) ≤ P) (d : ℕ) :
    I.refilteredProjectionImage i U d ∈
      heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
  have hdim : (Fintype.card (Fin (finrank ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))) : ℝ) ≤ P := by
    simpa only [Fintype.card_fin] using hF.1.1
  obtain ⟨a, ha⟩ := (pi (I.productModels i)).filtration.exists_refiltration_bases_in_coordinates
    F.basis F.weight F.layers (pi (I.productModels i)).basis U v hspan hP hdim hdim hv hforward d
  let z := fun j => I.rankProjection i (a j).val
  have hz : Submodule.span ℚ (Set.range z) = I.refilteredProjectionImage i U d := by
    have hsource := span_submodule_basis ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U d) a
    calc
      _ = (Submodule.span ℚ (Set.range (fun j => (a j).val))).map (I.rankProjection i).toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = _ := congrArg (fun K => K.map (I.rankProjection i).toLinearMap) hsource
  apply bounded_submodule_spanning_mem_candidates W.fourRankBasis _ z hz
    (one_le_ceil_exp (refiltrationCoordinateBudget P))
  intro j k
  apply rationalHeightLE_ceil_exp
  exact I.rankProjection_coordinates_logHeight i (a j).val (ha j) k

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem real_rankProjection_coordinates
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    (j : Σ _ : Fin 4, Fin W.dim) :
    (W.fourRankBasis.baseChange ℝ).repr ((I.rankProjection i).toLinearMap.baseChange ℝ x) j =
      ((pi (I.productModels i)).basis.baseChange ℝ).repr x
        ((Fintype.equivFin (Σ k : Option (Fin 4),
          Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
          ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
    exact congrArg (fun q : ℚ => q • a) (I.rankProjection_coordinates i x j)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem real_rankProjection_abs_bound
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    {B : ℝ} (hx : ∀ j, |((pi (I.productModels i)).basis.baseChange ℝ).repr x j| ≤ B)
    (j : Σ _ : Fin 4, Fin W.dim) :
    |(W.fourRankBasis.baseChange ℝ).repr ((I.rankProjection i).toLinearMap.baseChange ℝ x) j| ≤ B := by
  rw [I.real_rankProjection_coordinates i]
  exact hx _

theorem real_rankProjection_grid (l : ℕ)
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    (hx : (fun j => ((pi (I.productModels i)).basis.baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    (fun j => (W.fourRankBasis.baseChange ℝ).repr
      ((I.rankProjection i).toLinearMap.baseChange ℝ x) j) ∈ realDenominatorGrid l := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun j => a ((Fintype.equivFin (Σ k : Option (Fin 4),
    Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
      ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩), ?_⟩
  funext j
  exact (congrFun ha _).trans
    (congrArg (fun y : ℝ => (l : ℝ) * y) (I.real_rankProjection_coordinates i x j)).symm

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

namespace SunflowerWitness

variable {I : NativeRankInterval W out H t branch p q} {P : ℝ} 

end SunflowerWitness

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

noncomputable def projectedCoefficient (i : Fin I.expansion.count) (α : Unit →₀ ℕ) :
    (pi (I.productModels i)).filtration.PolynomialSymbol (fun _ : Unit => 1) →ₗ[ℚ]
      (Fin 4 → W.rank.filtration.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) α)) :=
  W.rank.filtration.projectedHorizontalSymbolCoefficient (pi (I.productModels i)).filtration
    (I.rankProjection i) (I.rankProjection_mem_layer i) (fun _ => 1) α

namespace SunflowerWitness

variable {I} {P : ℝ} 

end SunflowerWitness

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} 

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} 

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} 
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

variable {A κ : Type*} {s r : ℕ} {b : ℝ} (W : NativeDegreeRankFamily s r A b)

theorem logCoefficient_mem_rank_one (α : Unit →₀ ℕ) (a : A) :
    coefficients (W.orbit a).log α ∈
      (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ := by
  have h := W.rank.filtration.polynomialOrbit_coefficient_mem_rank_one (fun _ : Unit => 1) α
    (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a))
  exact (congrArg (fun z => coefficients z α ∈
    (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ)
    (W.rank.orbitEquiv_log (fun _ : Unit => 1) (W.orbit a))).mp h

theorem horizontalCoefficient_real_log (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) (α : Unit →₀ ℕ) (a : A)
    (v : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ)
    (hv : v.val = coefficients (W.orbit a).log α) :
    W.horizontalCoefficient hs c τ hG α a =
      W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) v := by
  apply W.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs c τ hG
    (fun _ : Unit => 1) α (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a)) v
  exact hv.trans (congrArg (fun z => coefficients z α)
    (W.rank.orbitEquiv_log (fun _ : Unit => 1) (W.orbit a))).symm

end NativeDegreeRankFamily

namespace NativeRankInterval.SunflowerWitness

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} 

end NativeRankInterval.SunflowerWitness
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

theorem exists_common_rank_relation_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → p + (p + c) ^ c ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  exact ⟨C, hC, fun p hp => by simpa [Polynomial.eval₂_pow] using hbudget p hp⟩

theorem exists_native_common_rank_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := p + (p + a) ^ a + 2
      q ≤ (p + C) ^ C ∧ (q + c) ^ c ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hsum : q + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Y, q, Polynomial.eval₂_pow] using hbudget p hp
  constructor <;> linarith only [hq, hpow, hsum]

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_common_data_budget (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + c) ^ c ≤ (p + C) ^ C ∧
      3 * (4 * p) * (4 * p) * (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) ≤
        (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C c) ^ c
  let A := ((Y + 1 + (Y + 3) ^ 7 + 2) ^ 9 + Y + 4) ^ 4
  let P := Y + 3 * (4 * X) * (4 * X) * (A + 2) * Polynomial.C (s + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hY : 0 ≤ (p + c) ^ c := by positivity
  have hA := refiltrationCoordinateBudget_nonneg hY
  have hcost : 0 ≤ 3 * (4 * p) * (4 * p) *
      (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) := by positivity
  have hsum : (p + c) ^ c + 3 * (4 * p) * (4 * p) *
      (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) ≤ (p + C) ^ C := by
    simpa [P, A, Y, X, refiltrationCoordinateBudget, Polynomial.eval₂_pow] using hbound p hp
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

namespace CommonData

variable {R : NativeRankRelation W out H p q} {P Q : ℝ} 

end CommonData

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankHorizontalRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem exists_rank_two_basis (d : Fin (s + 1)) (hd : 1 ≤ d.val) {p : ℝ}
    (hR : R.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (R.filtration.layer d.val 2))) ℚ (R.filtration.layer d.val 2),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  by_cases hs : 2 < s + 1
  · exact ⟨R.basis d ⟨2, hs⟩, hR.2 d ⟨2, hs⟩⟩
  · have hbot : R.filtration.layer d.val 2 = ⊥ := by
      apply bot_unique
      calc
        R.filtration.layer d.val 2 ≤ R.filtration.layer s (r + 1) :=
          R.filtration.lex_antitone (Or.inr ⟨by omega, by have hr := R.filtration.rank_le_degree; omega⟩)
        _ = ⊥ := R.filtration.terminal
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    let b := Module.finBasis ℚ (R.filtration.layer d.val 2)
    refine ⟨b, fun j k => ?_⟩
    have hb : (b j : L) = 0 := by
      have h := (b j).property
      simpa only [hbot, Submodule.mem_bot] using h
    rw [hb]
    simpa [rationalLogHeight] using (Nat.cast_nonneg n).trans hR.1.1

theorem exists_horizontal_ambient_basis (d : Fin (s + 1)) (hd : 1 ≤ d.val)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ Real.exp ((p + 3) ^ 7) ∧
      ∃ m : ℕ, m ≤ n ∧ ∃ f : Basis (Fin m) ℚ (L ⧸ R.filtration.layer d.val 2),
        ∀ i j, RationalHeightLE (f.repr ((R.filtration.layer d.val 2).mkQ (D.basis j)) i) H := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := R.exists_rank_two_basis d hd hR
  have hdim : (finrank ℚ (R.filtration.layer d.val 2) : ℝ) ≤ p + 1 := by
    calc
      _ ≤ (finrank ℚ L : ℝ) := by exact_mod_cast Submodule.finrank_le (R.filtration.layer d.val 2)
      _ = n := by rw [finrank_eq_card_basis D.basis, Fintype.card_fin]
      _ ≤ p + 1 := hR.1.1.trans (by linarith)
  obtain ⟨H, hH, hHp, m, hm, f, hf⟩ := exists_submodule_quotient_basis_exp D.basis
    (R.filtration.layer d.val 2) (fun j => (b j : L))
    (span_submodule_basis (R.filtration.layer d.val 2) b) (one_le_ceil_exp p)
    (fun j k => rationalHeightLE_ceil_exp (hb j k)) (by linarith : 0 ≤ p + 1)
    (by simpa only [Fintype.card_fin] using hdim) (ceil_exp_le_exp_add_one hp)
  refine ⟨H, hH, ?_, m, ?_, f, hf⟩
  · convert hHp using 2
    ring
  · simpa only [Fintype.card_fin] using hm

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem exists_controlled_horizontal_representatives
    {σ : Type*} (d : Fin (s + 1)) (hd : 1 ≤ d.val)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    {t : ℕ} (ht : t ≤ n) (f : Basis (Fin t) ℚ (L ⧸ R.filtration.layer d.val 2))
    (hf : ∀ i j, rationalLogHeight (f.repr ((R.filtration.layer d.val 2).mkQ (D.basis j)) i) ≤ p)
    {l : ℕ} (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget ((p + 3) ^ 4)) ≤ T i) :
    let P : ℝ := (p + 3) ^ 4
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 →
        ∀ (x y z : ℝ ⊗[ℚ] R.filtration.HigherHorizontal d.val) (a q : Fin t → ℝ),
        R.filtration.realHigherHorizontalCoordinates d.val f (x - y - z) = a + q →
        ‖a‖ ≤ Real.exp P / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : (R.filtration.layer d.val 1).baseChange ℝ,
          R.filtration.realHigherHorizontalCoordinates d.val f
            (R.filtration.realHorizontalMap d.val E) = a ∧
          R.filtration.realHigherHorizontalCoordinates d.val f
            (R.filtration.realHorizontalMap d.val Q) = q ∧
          x - y - R.filtration.realHorizontalMap d.val E -
            R.filtration.realHorizontalMap d.val Q = z ∧
          ‖(D.basis.baseChange ℝ).equivFun E.val‖ ≤
            Real.exp ((P + 2) ^ 3 + (P + 2) ^ 18 + P) / monomialScale T α ∧
          (D.basis.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid m := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := R.basis d ⟨1, by omega⟩
  let v : Fin (finrank ℚ (R.filtration.layer d.val 1)) → L := fun j => b j
  let K := ⌈Real.exp p⌉₊
  let H := max K ((n + 1) * (K * K) ^ n)
  let P : ℝ := (p + 3) ^ 4
  have hP : p + 1 ≤ P := by
    simpa only [P, show p + 1 + 2 = p + 3 by ring] using
      le_power_budget (p := p + 1) (by linarith) (by decide : 1 ≤ 4)
  have hpP : p ≤ P := (by linarith : p ≤ p + 1).trans hP
  have hn : (n : ℝ) ≤ p := hR.1.1
  have hvdim : finrank ℚ (R.filtration.layer d.val 1) ≤ n := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      Submodule.finrank_le (R.filtration.layer d.val 1)
  have hH : 1 ≤ H := (one_le_ceil_exp p).trans (Nat.le_max_left _ _)
  have hHP : (H : ℝ) ≤ Real.exp P := by
    change ((max K (replicatedFrequencyHeight n K) : ℕ) : ℝ) ≤ Real.exp P
    rw [Nat.cast_max]
    exact max_le ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hP))
      (replicatedFrequencyHeight_ceil_exp n hp hn)
  have hvH : ∀ j i, RationalHeightLE (D.basis.repr (v j) i) H := by
    intro j i
    exact (rationalHeightLE_ceil_exp (hR.2 d ⟨1, by omega⟩ j i)).mono (Nat.le_max_left _ _)
  have hfH : ∀ j i,
      RationalHeightLE (R.filtration.ambientHorizontalCoordinates d.val f (v j) i) H := by
    intro j i
    have h := linearMap_coordinate_height D.basis f (R.filtration.layer d.val 2).mkQ
      (fun j i => rationalHeightLE_ceil_exp (hf i j)) (v j)
      (fun i => rationalHeightLE_ceil_exp (hR.2 d ⟨1, by omega⟩ j i)) i
    exact (show RationalHeightLE
      (R.filtration.ambientHorizontalCoordinates d.val f (v j) i)
      ((n + 1) * (K * K) ^ n) from by
        simpa only [Fintype.card_fin, DegreeRankLieFiltration.ambientHorizontalCoordinates,
          LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_apply] using h).mono
        (Nat.le_max_right _ _)
  exact R.filtration.exists_controlled_horizontal_lifts d.val f D.basis v
    (span_submodule_basis _ b) hH hl hvH hfH (hp.trans hpP)
    (by simpa only [Fintype.card_fin] using hn.trans hpP)
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr ht).trans (hn.trans hpP))
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hvdim).trans (hn.trans hpP))
    hHP (hlp.trans (Real.exp_le_exp.mpr hpP)) T hT

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

end


