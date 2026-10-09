-- Prove2me | Definitions.Def_OAIErdos3B126
-- name    : OAIErdos3B126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T07:54:17.729108+00:00
-- url     : https://prove2.me/theorems/86c187b1-04bc-41f5-8009-cf5f29d18a98
-- title:
--   OpenAI Erdős-3 split, definitions bundle 127 of 132
-- statement:
--   Definitions bundle 127 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B125`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 127 available.
--
--   Modules: `OAI.Erdos3.CommonFixedNativeSquareFamilySpec`, `OAI.Erdos3.CommonNativeSquareFamilySpec`, `OAI.Erdos3.DegreeRankLieFiltration.integralGridDegreeRank`, `OAI.Erdos3.DegreeRankLieFiltration.integralGridDegreeRank_complexity`, `OAI.Erdos3.DegreeRankLieFiltration.integralGridNilmanifold`, `OAI.Erdos3.DegreeRankLieFiltration.integralGridNilmanifold_coordinates`, `OAI.Erdos3.DegreeRankLieFiltration.tailLayerBasis`, `OAI.Erdos3.DegreeRankLieFiltration.tailLayerBasis_height`, `OAI.Erdos3.InductiveNativeSquareFamilySpec`, `OAI.Erdos3.NativeDegreeRankFamily.component`, `OAI.Erdos3.NativeDegreeRankFamily.component_complexity`, `OAI.Erdos3.NativeDegreeRankFamily.component_eval`, `OAI.Erdos3.NativeDegreeRankFamily.lowerComponent`, `OAI.Erdos3.NativeDegreeRankFamily.lowerComponent_complexity`, `OAI.Erdos3.NativeDegreeRankFamily.lowerComponent_eval`, `OAI.Erdos3.NativeDegreeRankFamily.lowerComponent_evalCyclic`, `OAI.Erdos3.NativeDegreeRankFamily.rankZero_top_eq_bot`, `OAI.Erdos3.NativeMultidegreeNilcharacter.antisymmetricKernel`, `OAI.Erdos3.NativeMultidegreeNilcharacter.antisymmetricKernel_cyclic`, `OAI.Erdos3.NativeMultidegreeNilcharacter.antisymmetricKernel_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.component`, `OAI.Erdos3.NativeMultidegreeNilcharacter.component_complexity`, `OAI.Erdos3.NativeMultidegreeNilcharacter.component_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_antisymmetric_coordinate_slice`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_dilation_family`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_linear_niltest`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_coordinate_slice`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_multidegree_integer_translation`, `OAI.Erdos3.NilpotentLieFiltration.exists_square_quotient_niltest_with_orbit`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbit_coefficient_bound_value`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbit_coefficient_grid_value`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.rebaseNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.rebaseNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_adapted_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_rankInvariant_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_rankInvariant_niltest_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.rescale`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_dilation_family`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_prepared_dilation_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.dropTop`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.dropTop_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.dropTop_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_unit_bounded_vertical_mean_row`, `OAI.Erdos3.RationalFilteredNilmanifold.RefilteredResidueExpansionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_integer_translation_equivalence_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_shifted_product_expansion`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.test`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.test_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.test_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTopMap`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTopMap_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTopMap_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTopMap_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTopRealOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_bounded_frozen_constants`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_marked_kernel_residue_representatives`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_square_niltest_with_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_square_niltest_with_budget_and_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_square_niltest_with_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model`, `OAI.Erdos3.UniformNativeBiasedSquareSpec`, `OAI.Erdos3.cyclicDivision`, `OAI.Erdos3.cyclicDivision_val`, `OAI.Erdos3.cyclicDivision_with_residue_injective`, `OAI.Erdos3.cyclicHalf`, `OAI.Erdos3.cyclicHalf_val`, `OAI.Erdos3.cyclicHalf_with_parity_injective`, `OAI.Erdos3.exists_common_fixed_native_square_family`, `OAI.Erdos3.exists_common_native_square_family`, `OAI.Erdos3.exists_controlled_nilmanifold_of_tails`, `OAI.Erdos3.exists_controlled_normalized_square`, `OAI.Erdos3.exists_free_degree_rank_nilmanifold`, `OAI.Erdos3.exists_inductive_native_square_family`, `OAI.Erdos3.exists_native_shared_frozen_orbit_correlations`, `OAI.Erdos3.exists_residue_class_right_lattice_factors`, `OAI.Erdos3.exists_shared_factor_correlations`, `OAI.Erdos3.exists_uniform_native_biased_square`, `OAI.Erdos3.exists_uniform_two_shift_square`, `OAI.Erdos3.exists_vertical_derivative_detection`, `OAI.Erdos3.expect_cyclicDivision_le`, `OAI.Erdos3.expect_cyclicHalf_le`, `OAI.Erdos3.expect_fin_two`, `OAI.Erdos3.expect_pair_cyclicDivision_le`, `OAI.Erdos3.expect_pair_cyclicHalf_le`, `OAI.Erdos3.le_rankAdaptedNiltestBudget`, `OAI.Erdos3.norm_correlation_partition_bound`, `OAI.Erdos3.rankAdaptedNiltestBase`, `OAI.Erdos3.rankAdaptedNiltestBudget`, `OAI.Erdos3.right_lattice_factor_mk_eq`, `OAI.Erdos3.scaledIntegerGrid_le_denominatorGrid`, `OAI.Erdos3.sharedFactorCorrelationConstant`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B127

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_square_quotient_niltest_with_orbit
    (b : Basis (Fin m) ℚ F.squareLieSubalgebra) (v : Fin m → ℕ)
    (hlayers : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (F.squareLattice Γ))
    (hout : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid N)
    (w : σ → ℕ) (q : F.squareFiltration.realification.PolynomialOrbit w)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) N hN hout
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
    ∀ H : ℕ, 1 ≤ H →
      (∀ i j, RationalHeightLE (D.basis.repr
        (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H) →
      (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
    ∃ T : D.Niltest w,
      T.orbit = F.squareFiltration.realQuotientPolynomialOrbit
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
      (∀ z : F.squareFiltration.realification.Group,
        T.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
          F.realSquareObservable Γ ε u (QuotientGroup.mk z)) ∧
      T.normBound = B ^ 2 ∧
      T.lipBound = rationalReconstructionLipschitzBound s m
        (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2) ∧
      ∀ x : σ → ℤ, T.eval x = F.realSquareObservable Γ ε u
        (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  dsimp only
  intro H hH he hc
  let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
  obtain ⟨f, hf, hfLip, hfBound⟩ := F.exists_lipschitz_realSquare_descent Γ
    b D.basis N N H hN hN hH hout D.outer_grid he hc ε u χ hu A B hLip hb
  let K := rationalReconstructionLipschitzBound s m
    (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2)
  let T : D.Niltest w := {
    orbit := F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q
    observable := f
    normBound := B ^ 2
    lipBound := K
    norm_le := fun x => by simpa only [NNReal.coe_pow] using hfBound x
    lipschitz := by
      let : MetricSpace (F.squareFiltration.quotientTop.realification.Group ⧸
          ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
            (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :=
        realificationQuotientMetricSpace D.basis _ N hN D.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin, K]; exact le_rfl) }
  refine ⟨T, rfl, hf, rfl, rfl, ?_⟩
  intro x
  change f (QuotientGroup.mk ((F.squareFiltration.quotientTop.realification.polynomialOrbitEval w x)
    (F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q))) = _
  exact (congrArg (fun g : F.squareFiltration.quotientTop.realification.Group =>
      f (QuotientGroup.mk g))
    (F.squareFiltration.realQuotientPolynomialOrbit_eval
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q x)).trans (hf _)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem exists_uniform_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c)) :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout
      Q.GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
        (χ : D.RealGroup → CircleFourier.Circle),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ (A : ℝ≥0), (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) →
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) →
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeom, hgeomQ⟩ :=
    D.exists_controlled_reduced_square_geometry hp hT.1
  let m := Fintype.card (Fin (finrank ℚ L) ⊕ {i // 2 ≤ v₀ i})
  let bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra := D.filtration.squareFinBasis b₀ v₀ (hlayers 2)
  let v : Fin m → ℕ := squareFinWeight v₀
  have hls := D.filtration.squareFinBasis_layers b₀ v₀ hlayers
  let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
    (D.filtration.squareLattice D.lattice) N hN hin hout
  refine ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeomQ, ?_⟩
  intro ε q χ hvert A hA hALip
  have hQ : Q.GeometryComplexityLE (squareGeometryBudget p) := hgeomQ
  have hm : (m : ℝ) ≤ squareGeometryBudget p := hgeom.1
  have hQ0 := squareGeometryBudget_nonneg hp
  have hObs0 := normalizedSquareObservableBudget_nonneg a b hp
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  let Hproj := ⌈Real.exp (p + 1)⌉₊
  have hproj := D.filtration.squareFinBasis_projection_height D.basis b₀ v₀ (hlayers 2)
    (one_le_ceil_exp (p + 1)) (fun i j => rationalHeightLE_ceil_exp (hb₀ j i))
  let P := coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin m)) Hproj
  have hP : (P : ℝ) ≤ Real.exp (normalizedSquareProjectionBudget p) := by
    have heq : normalizedSquareProjectionBudget p = (squareGeometryBudget p + p + 2 + 2) ^ 2 := by
      unfold normalizedSquareProjectionBudget
      ring
    rw [heq]
    apply coordinateLipschitzBound_le_exp _ _ Hproj
      (show 0 ≤ squareGeometryBudget p + p + 2 by linarith)
    · simpa only [Fintype.card_fin] using hT.1.1.trans (by linarith : p ≤ squareGeometryBudget p + p + 2)
    · simpa only [Fintype.card_fin] using hm.trans (by linarith : squareGeometryBudget p ≤ squareGeometryBudget p + p + 2)
    · exact (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
        (Real.exp_le_exp.mpr (by linarith))
  let ℓ := T.normBound * (T.lipBound * P) + T.normBound * (T.lipBound * (A * P))
  have hℓLip : letI := realificationQuotientMetricSpace bs (D.filtration.squareLattice D.lattice) N hN hout
      LipschitzWith ℓ (D.filtration.realSquareObservable D.lattice ε T.observable) :=
    D.filtration.realSquareObservable_lipschitz D.basis bs D.lattice D.grid N Hproj D.grid_pos hN
      D.outer_grid hout (fun k i => (hproj i k).1) (fun k i => (hproj i k).2)
      ε T.observable A T.lipBound T.normBound hALip T.lipschitz T.norm_le
  have hℓ : (ℓ : ℝ) ≤ Real.exp (normalizedSquareObservableBudget a b p) :=
    squareObservableLipschitz_le_exp A T.normBound T.lipBound P
      (normalizedSquareLeftBudget_nonneg a b hp) hA hB hK hP
  let H := ⌈Real.exp (squareGeometryBudget p)⌉₊
  have he (i j) : RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1)) (bs j)) i) H := by
    exact (quotientFinBasis_projection_height bs
      (D.filtration.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ v i}
      (hls (s + 1)) j i).mono (one_le_ceil_exp _)
  obtain ⟨S, hOrbit, hObs, hSB, hSK, hSval⟩ := D.filtration.exists_square_quotient_niltest_with_orbit D.lattice
    bs v hls N hN hin hout w q ε T.observable χ hvert ℓ T.normBound hℓLip T.norm_le
    H (one_le_ceil_exp _) he (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  let r := normalizedSquareReconstructionBudget a b p
  have hr : 0 ≤ r := normalizedSquareReconstructionBudget_nonneg a b hp
  have hQr : squareGeometryBudget p + 1 ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hUr : normalizedSquareObservableBudget a b p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hpr : 2 * p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hB2 : (((T.normBound ^ 2 : ℝ≥0) : ℝ)) ≤ Real.exp (2 * p) := by
    rw [NNReal.coe_pow]
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ T.normBound.coe_nonneg hB 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hSKBound : (S.lipBound : ℝ) ≤ Real.exp ((r + c) ^ c) := by
    rw [hSK]
    apply hrec _ _ H ℓ (T.normBound ^ 2) r hr
    · exact hm.trans (by linarith)
    · exact hQ.1.trans (by linarith)
    · exact (ceil_exp_le_exp_add_one hQ0).trans (Real.exp_le_exp.mpr hQr)
    · exact hℓ.trans (Real.exp_le_exp.mpr hUr)
    · exact hB2.trans (Real.exp_le_exp.mpr hpr)
  have hSBBound : (S.normBound : ℝ) ≤ Real.exp (2 * p) := by rw [hSB]; exact hB2
  have hlog := niltest_log_bound_of_exp S.normBound S.lipBound
    (by linarith : 0 ≤ 2 * p) (by positivity : 0 ≤ (r + c) ^ c) hSBBound hSKBound
  refine ⟨S, hOrbit, hObs, hSB, ?_, hSval⟩
  constructor
  · apply hQ.mono
    change squareGeometryBudget p ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    have hpow : 0 ≤ (r + c) ^ c := by positivity
    linarith
  · apply hlog.trans
    change 2 * p + (r + c) ^ c + 4 ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    linarith

theorem exists_square_niltest_with_budget_and_orbit {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c))
    (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p))
    (hALip : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
      (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, _, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  obtain ⟨S, hS⟩ := hconstruct ε q χ hvert A hA hALip
  exact ⟨_, D.filtration.squareFinBasis e ω (hF 2), squareFinWeight ω,
    D.filtration.squareFinBasis_layers e ω hF, N, hN, hin, hout, S, hS⟩

theorem exists_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c))
    (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p))
    (hALip : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
      (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest w, S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, _, _, hS⟩ :=
    D.exists_square_niltest_with_budget_and_orbit T hp hT a b c hrec ε q χ hvert A hA hALip
  exact ⟨m, bs, v, hls, N, hN, hin, hout, S, hS⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct NNReal

universe uσ uι uL

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedVerticalExpansion
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p → ∀ (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      ∀ h : σ → ℤ, ∃ (n : ℕ)
        (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n)
        (S : Q.Niltest w),
        S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x : σ → ℤ, S.eval x = T.eval (fun i => x i + h i) * star (T.eval x) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT χ hvert h
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw h T.orbit
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, hSB, hS, hSval⟩ :=
    D.exists_square_niltest_with_budget T hp hT a b c hrec ε q χ hvert A hA (hALip ε hε)
  refine ⟨_, _, S, hSB, hS.mono (hbudget p hp), ?_⟩
  intro x
  exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
    (D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) T.orbit)
    (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
    (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_uniform_two_shift_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∃ (n : ℕ) (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n),
        Q.GeometryComplexityLE (squareGeometryBudget p) ∧
        ∀ (χ : D.RealGroup → CircleFourier.Circle),
          (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
            T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ a b : σ → ℤ, ∃ S : Q.Niltest w,
          S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
          ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b)) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  refine ⟨_, _, hgeom, ?_⟩
  intro χ hvert h k
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw (h - k) T.orbit
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨S, _, _, hSB, hS, hSval⟩ := hconstruct ε q χ hvert A hA (hALip ε hε)
  have hval (x : σ → ℤ) : S.eval x = T.eval (x + (h - k)) * star (T.eval x) := by
    exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
      (D.filtration.realification.polynomialOrbitEval w (fun i => x i + (h - k) i) T.orbit)
      (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
      (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)
  refine ⟨S.translate hw k, hSB, hS.mono (hbudget p hp), ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_translate, hval]
  congr 2
  abel

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

universe u v

theorem exists_vertical_derivative_detection (s : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ c : ℕ,
      BoxNiltestDetection.{u,v} s (fun q => (q + c) ^ c) →
      ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u}
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (p q : ℝ),
      0 ≤ p → 0 ≤ q → (Fintype.card σ : ℝ) ≤ q → (p + b) ^ b ≤ q →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) → ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∀ (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      ∀ (h a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
      (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
      Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f (multiplicativeDerivative T.eval h)‖ →
      Real.exp (-((q + c) ^ c)) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f := by
  obtain ⟨b, hb, hsq⟩ := exists_controlled_normalized_square s
  refine ⟨b, hb, ?_⟩
  intro c hI σ _ _ L _ _ d _ _ _ _ D p q hp hq hσ hcost w hw T hT χ hvert h a lengths _ f hf hc
  let K := D.filtration.squareLieSubalgebra
  let M := K ⧸ D.filtration.squareFiltration.layerIdeal (s + 1)
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ K := inferInstance
  let : FiniteDimensional ℚ M := inferInstance
  let : TopologicalSpace (ℝ ⊗[ℚ] K) := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] K) := inferInstance
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 (Module.finBasis ℚ K)
  let : TopologicalSpace (ℝ ⊗[ℚ] M) := moduleTopology ℝ (ℝ ⊗[ℚ] M)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M) := IsModuleTopology.topologicalAddGroup ℝ _
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] M) := inferInstance
  let : T2Space (ℝ ⊗[ℚ] M) := realification_moduleTopology_t2 (Module.finBasis ℚ M)
  obtain ⟨n, E, S, _, hS, hval⟩ := hsq D p hp w hw T hT χ hvert h
  have heval : S.conjugate.eval = multiplicativeDerivative T.eval h := by
    funext x
    rw [RationalFilteredNilmanifold.Niltest.eval_conjugate, hval]
    simp only [multiplicativeDerivative, star_mul, star_star]
    rfl
  have hc' : Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f S.conjugate.eval‖ := by
    rwa [heval]
  exact hI E q hq hσ w hw S.conjugate (hS.mono hcost) a lengths f hf hc'

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_shifted_product_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      {p : ℝ} (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → D.GeometryComplexityLE p → (∀ k, 0 < w k) → ∀ (i j : I) (a b : σ → ℤ),
      ∃ (n : Fin 4 → ℕ)
        (Q : ∀ k, RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s (n k))
        (S : ∀ k, (Q k).Niltest w),
        (∀ k, (S k).normBound = 4) ∧ (∀ k, (S k).ComplexityLE ((p + C) ^ C)) ∧
        ∀ x, V.observable i (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w (x + a) g)) *
          star (V.observable j (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w (x + b) g))) =
          ∑ k, polarizationWeight k * (S k).eval x := by
  obtain ⟨A, _, hsquare⟩ := exists_uniform_two_shift_square s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + 5 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D _ _ _ _ _ _ _ _ p V w g hp hD hw i j a b
  have hbound : (p + 5 + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  let T : Fin 4 → D.Niltest w := fun k =>
    V.combinationNiltest g i j (polarizationPhase k) (polarizationPhase_norm k).le
  have hparts : ∀ k, ∃ (n : ℕ)
      (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)) s n) (S : Q.Niltest w),
      S.normBound = 4 ∧ S.ComplexityLE ((p + C) ^ C) ∧
      ∀ x, S.eval x = (T k).eval (x + a) * star ((T k).eval (x + b)) := by
    intro k
    obtain ⟨n, Q, _, hconstruct⟩ := hsquare D (p + 5) (by linarith) w hw (T k)
      (V.combinationNiltest_complexity g i j _ _ hp hD)
    obtain ⟨S, hSn, hSc, hSe⟩ := hconstruct
      (fun z => ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle))
      (fun z hz x => V.coordinateCombination_vertical i j (polarizationPhase k) z hz x) a b
    refine ⟨n, Q, S, ?_, hSc.mono hbound, hSe⟩
    calc
      S.normBound = (T k).normBound ^ 2 := hSn
      _ = 4 := by norm_num [T, combinationNiltest]
  choose n Q S hSn hSc hSe using hparts
  refine ⟨n, Q, S, hSn, hSc, ?_⟩
  intro x
  refine (complex_mixed_polarization _
    (V.observable j (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (x + a) g)))
    (V.observable i (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (x + b) g))) _).trans ?_
  apply Finset.sum_congr rfl
  intro k _
  rw [hSe k x]
  rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFixedNativeSquareFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def UniformNativeBiasedSquareSpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (h : σ → ℤ) (A : Finset (σ → ℤ)), A.Nonempty →
        Real.exp (-(2 * p + 1)) ≤ ‖𝔼 x ∈ A, T.eval (x + h) * star (T.eval x)‖ →
        D.HasNativeBiasedSquareInModel
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η A h ((p + C) ^ C)

theorem exists_uniform_native_biased_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ UniformNativeBiasedSquareSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hnorm⟩ := exists_native_normalized_square.{uσ, 0, uL} s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨d, _, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  obtain ⟨v, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C d) ^ d +
    (Polynomial.X + 1 + Polynomial.C a) ^ a + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := R + (R + Polynomial.C v) ^ v + 2 * Polynomial.X + 2
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ n _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let q := (p + d) ^ d + (p + 1 + a) ^ a + 2 * p + 2
  have hd0 : 0 ≤ (p + d) ^ d := by positivity
  have ha0 : 0 ≤ (p + 1 + a) ^ a := by positivity
  have hdq : (p + d) ^ d ≤ q := by dsimp [q]; linarith
  have haq : (p + 1 + a) ^ a ≤ q := by dsimp [q]; linarith
  have hpq : 2 * p + 2 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hv := hvertical q hq
  have hpow : 0 ≤ (q + v) ^ v := by positivity
  have hfinal' : q + (q + v) ^ v + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [P, R, q, Polynomial.eval₂_pow] using hfinal p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hvC : verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  have hbC : 2 * p + 2 + verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  obtain ⟨A₀, _, hA₀, hLip⟩ := hleft D p hp hT.1
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert h A hA hbias
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative⟩ :=
    hnorm D e ω hF p hp hT.1 (fun i => (h i : ℚ)) g
  let qr := D.filtration.squareFiltration.nativePolynomialOrbit (fun _ : σ => 1) r
  obtain ⟨S, hOrbit, hObs, _, hS, hSval⟩ := hconstruct ε qr
    (fun z => ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle))
    hvert A₀ hA₀ (hLip ε hε)
  have hEval (x : σ → ℤ) : S.eval x = T.eval (x + h) * star (T.eval x) := by
    apply (hSval x).trans
    have hprod := D.filtration.nativeNormalizedSquareObservable_product (fun _ => 1)
      D.lattice h ε γ hγ T.observable g r hf hsecond x
    rw [hg] at hprod
    exact hprod
  have herror : (Real.exp (-(2 * p + 1)) / 2)⁻¹ ≤ Real.exp q := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp (2 * p + 1) := by rw [inv_div, Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (2 * p + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hpq
  have hc : Real.exp (-(2 * p + 1)) ≤ ‖finiteCorrelation A (fun _ => 1) S.eval‖ := by
    rw [norm_finiteCorrelation_one]
    have hmean : (𝔼 x ∈ A, S.eval x) = 𝔼 x ∈ A, T.eval (x + h) * star (T.eval x) :=
      Finset.expect_congr rfl (fun x _ => hEval x)
    rw [hmean]
    exact hbias
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hrestriction, hCorr⟩ :=
    D.filtration.exists_correlating_square_vertical_mode D.lattice
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hs (fun _ : σ => 1) ε η T.observable hvert r S hOrbit hObs hq
      (hS.mono ((hbudget p hp).trans hdq)) (Real.exp_pos _) herror hA
      (fun _ => 1) (fun _ _ => by norm_num) hc
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr (haq.trans hqC))),
    r, hf, hsecond, ?_, ξ, V, hVO, hV.mono hqC,
    (fun i => (hheight i).trans hvC), hchar, hint, hrestriction, ?_⟩
  · simpa only [Rat.cast_intCast] using hderivative
  · rw [norm_finiteCorrelation_one] at hCorr
    apply le_trans _ hCorr
    calc
      _ ≤ Real.exp ((-(2 * p + 1) - verticalDecompositionBudget q) - 1) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ Real.exp (-(2 * p + 1) - verticalDecompositionBudget q) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [Real.exp_sub]; ring

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def CommonNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ H : Finset (σ → ℤ), H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasNativeBiasedSquareInModel
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (derivativeSupport (translatedIntegerBox origin lengths) h) h ((p + C) ^ C)

theorem exists_common_native_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hsingle⟩ := exists_uniform_native_biased_square.{uσ, uL} s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + 5 * Polynomial.X + 6
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ n _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  have hbound : (p + a) ^ a + 5 * p + 6 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  have h5 : 5 * p + 6 ≤ (p + C) ^ C := by linarith
  have h4 : 4 * p + 6 ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hsingle hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert origin lengths hlengths hσ hbias
  obtain ⟨H, hH, hcount, hgood⟩ := exists_many_biased_box_shifts origin lengths hlengths T.eval hp hσ
    (fun x _ => T.eval_budget hT x) hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h4))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hmean⟩ := hgood h hh
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h5))
        (Nat.cast_nonneg (lengths i))).trans_lt (hsides i)
    · have hA : (derivativeSupport (translatedIntegerBox origin lengths) h).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.expect_empty, norm_zero] at hmean
        exact (not_le_of_gt (Real.exp_pos _)) hmean
      exact RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        (hconstruct g hg η hvert h (derivativeSupport (translatedIntegerBox origin lengths) h) hA hmean) haC

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

namespace RationalFilteredNilmanifold

theorem HasNativeFactoredSquareInModel.mono
    {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    {hs : 1 ≤ s} {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p q p' q' : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p q)
    (hpp : p ≤ p') (hqq : q ≤ q') (hS : ∀ i, 0 < S i) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p' q' := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpp)), r,
    hf, hsecond, hderivative, ξ, (fun i => (hheight i).trans hpp), hrestriction, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ _ _ _ hfactor hqq hS

theorem HasNativeFactoredSquareInModel.rescale
    {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    {hs : 1 ≤ s} {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ} {h : σ → ℤ} {p q r : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p q)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hr : 0 ≤ r) (hST : ∀ i, Real.exp (-r) * T i ≤ S i) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η T h p (q + (s : ℝ) * r) := by
  obtain ⟨ε, γ, hγ, hε, a, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  refine ⟨ε, γ, hγ, hε, a, hf, hsecond, hderivative, ξ, hheight, hrestriction, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.rescale _ _ _ _ hfactor hS hT hr hST

end RationalFilteredNilmanifold

def InductiveNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ H : Finset (σ → ℤ), H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasNativeFactoredSquareInModel
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (fun i => (lengths i : ℝ)) h ((p + C) ^ C) ((p + C) ^ C)

theorem exists_inductive_native_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ InductiveNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, ha, hfamily⟩ := exists_common_native_square_family.{uσ, uL} s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P : Polynomial ℕ := B + ((B + Polynomial.C c) ^ c + Polynomial.C s * B)
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let q : ℝ := (p + a) ^ a
  let r : ℝ := (q + c) ^ c
  let t : ℝ := r + (s : ℝ) * q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbound : q + t ≤ (p + C) ^ C := by
    simpa [P, B, q, r, t, Polynomial.eval₂_pow] using hfinal p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right ht).trans hbound
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  have hqr : q + r ≤ (p + C) ^ C := by
    have hrt : r ≤ t := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hq)
    exact (add_le_add (le_refl q) hrt).trans hbound
  have hpq : p ≤ q := by
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
    apply (show p ≤ p + a by linarith).trans
    exact (pow_one (p + a)).symm.le.trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + a) (by omega : 1 ≤ a))
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hfamily hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert origin lengths hlengths hσ hlarge hbias
  obtain ⟨H, hH, hcount, hgood⟩ := hconstruct g hg η hvert origin lengths hlengths hσ hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hdata⟩ := hgood h hh
    have hlargeOverlap : ∀ i, Real.exp r ≤ (((lengths i : ℤ) - |h i|).toNat : ℝ) := by
      intro i
      have hsize : Real.exp (q + r) ≤ (lengths i : ℝ) :=
        (Real.exp_le_exp.mpr hqr).trans (hlarge i)
      have heq : Real.exp r = Real.exp (-q) * Real.exp (q + r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le).trans (hsides i).le
    have hpos : ∀ i, 0 < ((lengths i : ℤ) - |h i|).toNat := by
      intro i
      have hposR := (Real.exp_pos r).trans_le (hlargeOverlap i)
      exact_mod_cast hposR
    rw [derivativeSupport_translatedIntegerBox] at hdata
    have hfactor := RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.factorization D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hI hq (hσ.trans hpq) hpos hlargeOverlap hdata
    have hscaled := RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.rescale D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hfactor
      (fun i => by exact_mod_cast hpos i) (fun i => by exact_mod_cast hlengths i)
      hq (fun i => (hsides i).le)
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
        (Nat.cast_nonneg (lengths i))).trans_lt (hsides i)
    · exact RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        hscaled hqC htC (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def CommonFixedNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF)
          (D.filtration.squareLattice D.lattice) N hN hin hout
        let ν := quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}
        let hQ := D.filtration.squareFiltration.topQuotientModel_basis_layers
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF)
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (H : Finset (σ → ℤ)) (l : ℕ) (W : LieSubalgebra ℚ Q.filtration.AssociatedGraded)
          (u : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) → Q.filtration.AssociatedGraded),
          H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule (Q.filtration.associatedGradedBasis Q.basis ν hQ) ν W.toSubmodule ∧
          BasisFamilyLogHeight (Q.filtration.associatedGradedBasis Q.basis ν hQ) u ((p + C) ^ C) ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasFixedNativeSquareFactors
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (fun i => (lengths i : ℝ)) h ((p + C) ^ C) l W

theorem exists_common_fixed_native_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonFixedNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_inductive_native_square_family s c hI
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + G
  let P : Polynomial ℕ := B + ((Q + 2) ^ 5 + Q) + Q
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let b : ℝ := (p + a) ^ a
  let q : ℝ := b + squareGeometryBudget p
  let k : ℝ := (q + 2) ^ 5 + q
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := add_nonneg hb hg
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbound : b + k + q ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, b, q, k, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hbkC : b + k ≤ (p + C) ^ C := by linarith
  have hbq : b ≤ q := le_add_of_nonneg_right hg
  have hgq : squareGeometryBudget p ≤ q := le_add_of_nonneg_left hb
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hfamily hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨H, hH, hcount, hgood⟩ := hconstruct g hgOrbit η hvert origin lengths hlengths hσ
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) hbias
  have hdata : ∀ h ∈ H, D.HasNativeFactoredSquareInModel
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h q q := by
    intro h hh
    exact RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      (hgood h hh).2.2 hbq hbq hTpos
  obtain ⟨l, W, u, H', hsub, hH', hlarge', hl, hlq, hu, hW, hheight, hfixed⟩ :=
    D.exists_common_native_square_factors
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hs g η (fun i => (lengths i : ℝ)) H hH hq (hgeom.1.trans hgq) hdata
  refine ⟨H', l, W, u, hH', ?_, hl, hlq.trans (Real.exp_le_exp.mpr hqC), hu, hW,
    ?_, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤
          Real.exp (-(b + k)) * (∏ i, (lengths i : ℝ)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbkC))
          (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))
      _ = Real.exp (-k) * (Real.exp (-b) * (∏ i, (lengths i : ℝ))) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-k) * H.card := mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
      _ ≤ H'.card := hlarge'
  · intro i j
    exact (hheight i j).trans hqC
  · intro h hh
    have hprior := hgood h (hsub hh)
    refine ⟨hprior.1, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbC))
        (Nat.cast_nonneg (lengths i))).trans_lt (hprior.2.1 i)
    · exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        (hfixed h hh) hqC hTpos

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCorrelatedFactorFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialOrbit_coefficient_grid_value (q : ℕ)
    (g : F.realification.PolynomialOrbit w) (hg : CoefficientGrid (b.baseChange ℝ) q g.log)
    (x : σ → ℤ) :
    (b.baseChange ℝ).equivFun (F.realification.polynomialOrbitEval w x g).coord ∈ realDenominatorGrid q := by
  have h := F.polynomialRationalGrid_value b w q (F.realification.polynomialOrbitCoordinates w g)
    ((F.polynomialRationalGrid_iff_formal b w q _).mpr hg) x
  simpa only [F.polynomialOrbitCoordinates_realValue] using h

omit [Fintype ι] in
theorem polynomialOrbit_coefficient_bound_value
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (hw : ∀ i, 0 < w i) (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.realification.PolynomialOrbit w) (hg : CoefficientBound (b.baseChange ℝ) T M g.log)
    (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ T i) (i : ι) :
    |(b.baseChange ℝ).repr (F.realification.polynomialOrbitEval w x g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M := by
  have h := F.polynomialSlowBound_value b w hw T hT hM (F.realification.polynomialOrbitCoordinates w g)
    ((F.polynomialSlowBound_iff_formal b w T M _).mpr hg) (fun j => (x j : ℝ)) hx i
  simpa only [F.polynomialOrbitCoordinates_realValue] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_frozen_constants (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ ε γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
            (Real.exp ((p + 2) ^ a)) ε.log →
          CoefficientGrid (D.basis.baseChange ℝ) q γ.log → ∀ y : ZMod N,
          (∀ i, |(D.basis.baseChange ℝ).repr
            (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (y.val : ℤ)) ε).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ δ ∈ D.realLattice,
              D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                (fun _ => (y.val : ℤ)) γ = r * δ := by
  obtain ⟨b, _, hrep⟩ := exists_native_rational_representatives s
  let k := (s + 1) * 2 ^ s
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + Polynomial.C k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp hD q hq hqp
  have htotal : (p + 2) ^ a + (k : ℝ) + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + b) ^ b := by positivity
  have hsmall : (p + 2) ^ a + (k : ℝ) ≤ (p + C) ^ C := by linarith
  have hrepC : (p + b) ^ b ≤ (p + C) ^ C := by
    have hpowa : 0 ≤ (p + 2) ^ a := by positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  obtain ⟨m, hm, hmp, hsolve⟩ := hrep D p hp hD q hq hqp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrepC), ?_⟩
  intro ε γ hε hγ y
  refine ⟨?_, ?_⟩
  · intro i
    have hv := D.filtration.polynomialOrbit_coefficient_bound_value D.basis (fun _ : Unit => 1)
      (fun _ => Nat.zero_lt_one) (fun _ : Unit => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (Real.exp_pos _).le ε hε
      (fun _ => (y.val : ℤ)) (fun _ => by
        simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ y.val from Nat.cast_nonneg _)]
          using (Nat.cast_le.mpr y.val_lt.le : (y.val : ℝ) ≤ N)) i
    have hke : (k : ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k : ℝ)]
    have hk : ((s : ℝ) + 1) * ((Fintype.card Unit : ℝ) + 1) ^ s = (k : ℝ) := by
      simp only [k, Fintype.card_unit, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      norm_num
    rw [hk] at hv
    exact hv.trans ((mul_le_mul_of_nonneg_right hke (Real.exp_pos _).le).trans
      (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)))
  · obtain ⟨⟨r, hr, hrgrid, δ, hδ, heq⟩, _⟩ := hsolve
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) γ)
      (D.filtration.polynomialOrbit_coefficient_grid_value D.basis (fun _ : Unit => 1) q γ hγ _)
    exact ⟨r, fun i => (hr i).trans (Real.exp_le_exp.mpr hrepC), hrgrid, δ, hδ, heq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem right_lattice_factor_mk_eq {G : Type*} [Group G] (Γ : Subgroup G)
    (a x u δ : G) (hδ : δ ∈ Γ) :
    (QuotientGroup.mk (a * x * (u * δ)) : G ⧸ Γ) = QuotientGroup.mk (a * x * u) := by
  apply QuotientGroup.eq.mpr
  convert Γ.inv_mem hδ using 1
  group

namespace RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_native_shared_frozen_orbit_correlations (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      0 ≤ P → p ≤ P → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp P →
      ∀ (H : Finset (ZMod N))
        (ε γ b : ZMod N → W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (y : ZMod N → ZMod N), H.Nonempty →
      (∀ h ∈ H, CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 2) ^ k)) (ε h).log) →
      (∀ h ∈ H, CoefficientGrid (W.family.model.basis.baseChange ℝ) q (γ h).log) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N P
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (b h) (γ h) (y h) x)))) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid m),
          (W.family.rank.withLattice Λ m hm hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (W.family.model.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ m hm hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                  (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (b h)))))) := by
  obtain ⟨a₀, _, hconstants⟩ := exists_bounded_frozen_constants s k
  obtain ⟨b₀, _, hshared⟩ := exists_native_shared_frozen_correlations s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a₀) ^ a₀ + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C b₀) ^ b₀)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P F W hF hP hpP q hq hqP H ε γ b y hH hε hγ hcorr
  classical
  let T := P + (P + a₀) ^ a₀ + 2
  have hA : 0 ≤ (P + a₀) ^ a₀ := by positivity
  have hPT : P ≤ T := by dsimp only [T]; linarith
  have hAT : (P + a₀) ^ a₀ ≤ T := by dsimp only [T]; linarith
  have hT : 0 ≤ T := hP.trans hPT
  have hsum : T + (T + b₀) ^ b₀ ≤ (P + C) ^ C := by
    simpa [Q, T, Polynomial.eval₂_pow] using hbudget P hP
  have hTC : (T + b₀) ^ b₀ ≤ (P + C) ^ C := by linarith
  obtain ⟨l, hl, hlbound, hsolve⟩ := hconstants (N := N) W.family.model P hP
    (W.family.complexity.1.mono _ hpP) q hq hqP
  have hreps (h : {h // h ∈ H}) := (hsolve (ε h) (γ h) (hε h h.property) (hγ h h.property) (y h)).2
  choose u hu hugrid δ hδ heq using hreps
  let u' (h : ZMod N) : W.family.model.RealGroup := if hh : h ∈ H then u ⟨h, hh⟩ else 1
  let a (h : ZMod N) := W.family.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => ((y h).val : ℤ)) (ε h)
  let b' (h x : ZMod N) := W.family.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (b h)
  have hbound : Real.exp ((P + a₀) ^ a₀) ≤ Real.exp ((T + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)
  have ha (h : ZMod N) (hh : h ∈ H) (i : Fin W.family.dim) :
      |(W.family.model.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((T + 2) ^ 1) :=
    ((hsolve (ε h) (γ h) (hε h hh) (hγ h hh) (y h)).1 i).trans hbound
  have hu' (h : ZMod N) (hh : h ∈ H) (i : Fin W.family.dim) :
      |(W.family.model.basis.baseChange ℝ).repr (u' h).coord i| ≤ Real.exp ((T + 2) ^ 1) := by
    simpa only [u', dif_pos hh] using (hu ⟨h, hh⟩ i).trans hbound
  have hugrid' (h : ZMod N) (hh : h ∈ H) :
      (W.family.model.basis.baseChange ℝ).equivFun (u' h).coord ∈ realDenominatorGrid l := by
    simpa only [u', dif_pos hh] using hugrid ⟨h, hh⟩
  have hc (h : ZMod N) (hh : h ∈ H) : Nonempty (NativeVectorCorrelation (s - 1) N T
      (W.replacedRankResidual h (fun i x => W.family.vertical.observable i
        (QuotientGroup.mk (a h * b' h x * u' h))))) := by
    have hfun : (fun i x => W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x * u' h))) =
        (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (b h) (γ h) (y h) x) := by
      funext i x
      change W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x * u' h)) =
        W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x *
          W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => ((y h).val : ℤ)) (γ h)))
      rw [heq ⟨h, hh⟩]
      simp only [u', dif_pos hh]
      exact congrArg (W.family.vertical.observable i)
        (right_lattice_factor_mk_eq W.family.model.realLattice (a h) (b' h x) (u ⟨h, hh⟩)
          (δ ⟨h, hh⟩) (hδ ⟨h, hh⟩)).symm
    rw [hfun]
    exact ⟨(Classical.choice (hcorr h hh)).mono hPT⟩
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, hU⟩ :=
    hshared W hF hT (hpP.trans hPT) l hl
      (hlbound.trans (Real.exp_le_exp.mpr hAT)) H a u' b' hH ha hu' hugrid' hc
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hTC),
    m, hm, hin, hout, hRank.mono _ hTC, H', hsub, hnonempty, ?_, U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hTC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact ⟨(Classical.choice (hU h hh)).mono hTC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_shared_factor_correlations (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      2 ≤ P → p ≤ P → ∀ (m M : ℕ), 0 < m → (m : ℝ) ≤ Real.exp P →
      0 < M → (M : ℝ) ≤ Real.exp P →
      ∀ (J : Finset (ZMod N)), J ⊆ W.shifts → J.Nonempty →
      ∀ ε a ρ : ZMod N → W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      (∀ h ∈ J, ε h * a h * ρ h = W.family.orbit h) →
      (∀ h ∈ J, CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp ((P + 2) ^ 1)) (ε h).log) →
      (∀ h ∈ J, CoefficientGrid (W.family.model.basis.baseChange ℝ) m (ρ h).log) →
      (∀ h ∈ J, ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) x (ρ h)) : W.family.model.Space) =
        QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) y (ρ h))) →
      Real.exp ((P + C) ^ C) ≤ (N : ℝ) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (l : ℕ) (hl : 0 < l)
          (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid l),
          (W.family.rank.withLattice Λ l hl hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ J' : Finset (ZMod N), J' ⊆ J ∧ J'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * J.card ≤ (J'.card : ℝ) ∧
            ∃ V : (W.family.model.withLattice Λ l hl hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ l hl hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              V.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ J', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                  (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (a h)))))) := by
  obtain ⟨b, _, hfreeze⟩ := exists_native_frozen_rank_correlation s 1 hs
  obtain ⟨c, _, hshared⟩ := exists_native_shared_frozen_orbit_correlations s 1
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (B + (B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P f W hf hP hpP m M hm hmP hM hMP J hJW hJ ε a ρ hprod hε hρ hperiod hN
  classical
  let P₁ := (P + b) ^ b + P + 2
  have hP0 : 0 ≤ P := by linarith
  have hb0 : 0 ≤ (P + b) ^ b := by positivity
  have hP₁ : 0 ≤ P₁ := by dsimp only [P₁]; positivity
  have hPP₁ : P ≤ P₁ := by dsimp only [P₁]; linarith
  have hbP₁ : (P + b) ^ b ≤ P₁ := by dsimp only [P₁]; linarith
  have hsum : P₁ + (P₁ + c) ^ c ≤ (P + C) ^ C := by
    simpa [P₁, B, Polynomial.eval₂_pow] using hbudget P hP0
  have hP₁C : P₁ ≤ (P + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P₁ + c) ^ c)).trans hsum
  have hcC : (P₁ + c) ^ c ≤ (P + C) ^ C := (le_add_of_nonneg_left hP₁).trans hsum
  have hchoose (h : {h // h ∈ J}) : ∃ y : ZMod N,
      Nonempty (NativeVectorCorrelation (s - 1) N P₁
        (W.replacedRankResidual h.val (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h.val) (a h.val) (ρ h.val) y x))) := by
    obtain ⟨y, _, hy⟩ := hfreeze W hf ⟨h.val, hJW h.property⟩ P hP hpP M hM hMP
      (ε h.val) (a h.val) 1 (ρ h.val) (by simpa only [mul_one] using hprod h.val h.property)
      (hε h.val h.property) (hperiod h.val h.property)
      ((Real.exp_le_exp.mpr (hbP₁.trans hP₁C)).trans hN)
    refine ⟨y, ?_⟩
    simpa only [mul_one] using
      (show Nonempty _ from ⟨(Classical.choice hy).mono hbP₁⟩)
  choose y hy using hchoose
  let y' (h : ZMod N) := if hh : h ∈ J then y ⟨h, hh⟩ else 0
  have hcorr (h : ZMod N) (hh : h ∈ J) :
      Nonempty (NativeVectorCorrelation (s - 1) N P₁
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (a h) (ρ h) (y' h) x))) := by
    simpa only [y', dif_pos hh] using hy ⟨h, hh⟩
  have hε' (h : ZMod N) (hh : h ∈ J) :
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P₁ + 2) ^ 1)) (ε h).log :=
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (hε h hh)
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using (show P + 2 ≤ P₁ + 2 by linarith)))
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
      hRank, J', hsub, hnonempty, hdense, V, hfreq, hV⟩ :=
    hshared W hf hP₁ (hpP.trans hPP₁) m hm
      (hmP.trans (Real.exp_le_exp.mpr hPP₁)) J ε ρ a y' hJ hε' hρ hcorr
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcC),
    l, hl, hin, hout, hRank.mono _ hcC, J', hsub, hnonempty, ?_, V.mono hcC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact ⟨(Classical.choice (hV h hh)).mono hcC⟩

noncomputable def sharedFactorCorrelationConstant (s : ℕ) (hs : 2 ≤ s) : ℕ :=
  (exists_shared_factor_correlations s hs).choose

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PreparedDilationNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (q : ℤ) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) (s + 1) r)
  (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
  (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  (Q : RationalFilteredNilmanifold
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map
    (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hEL hQF hQL

theorem exists_prepared_dilation_niltest {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection (q : ℚ) j (E.basis a)) k) ≤ p)
    (hQ : Q.GeometryComplexityLE p)
    (hq : ∀ j k, rationalLogHeight
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) ≤ p)
    (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp p)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) :
    ∃ T : Q.Niltest (fun _ : σ => 1), T.normBound = 1 ∧
      T.ComplexityLE (DilationBudget.total (s + 1) q (MultilinearityBudget.reconstructionExponent s) p) ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x =
        V.observable a₀ (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
          (fun i => q * x i) g)) *
        star (signedTensorProduct (q ^ (s + 1)) (fun j => V.observable (a j)
          (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))) := by
  let H := ⌈Real.exp p⌉₊
  let B : ℝ≥0 := ((q ^ (s + 1)).natAbs + 1 : ℝ≥0) *
    (V.lipBound * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩))
  have hLip : letI := E.metricSpace
      LipschitzWith B (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))) :=
    M.dilationObservable_lipschitz (q : ℚ) E hEL hp hD hE hheight
      (q ^ (s + 1)) ε (V.observable a₀) (fun j => V.observable (a j)) V.lipBound A
      (V.norm a₀) (fun j => V.norm (a j)) (V.lipschitz a₀) (fun j => V.lipschitz (a j)) hε
  obtain ⟨T, hTn, hTl, hTzero, hTe⟩ := M.exists_dilation_niltest_of_data q hs E hEF hEL Q hQF hQL
    (one_le_ceil_exp p) (fun j k => rationalHeightLE_ceil_exp (hq j k))
    (fun j k l => rationalHeightLE_ceil_exp (hQ.2.2.1 j k l)) V g ε γ hγ hfactor a₀ a B hLip
  have hB : (B : ℝ) ≤ Real.exp (DilationBudget.reconstruction (s + 1) q p) := by
    change (((q ^ (s + 1)).natAbs : ℝ) + 1) *
      (V.lipBound * (A * Real.exp ((p + 3) ^ 2))) ≤ _
    exact DilationBudget.observable_bound (s + 1) q hp V.lipBound A V.lip_bound hA
  exact ⟨T, hTn, DilationBudget.niltest_complexity Q T (s + 1) q r H B hp hQ hE.1
    (ceil_exp_le_exp_add_one hp) hB hTn hTl, hTzero, hTe⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultidegreeDilation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators NNReal

theorem exists_controlled_dilation_family (s : ℕ) (q : ℤ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ {σ I : Type*} {L : Type}
      [Fintype σ] [DecidableEq σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound) (_hs : ∑ j, bound j = t) (_ht : t = s + 1)
      {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
        (g : M.filtration.realification.PolynomialOrbit),
      ∃ R : NativeIntegerModelFamily (fun _ : σ => 1) s ((p + Z) ^ Z)
        (dilationTensorCrossProduct
          (fun j y => V.observable j
            (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g))) q t),
        R.dim ≤ 2 * d := by
  obtain ⟨C, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨Z, hZ, hbudget⟩ := DilationBudget.exists_full_bound (s + 1) q C
    (MultilinearityBudget.reconstructionExponent s)
  refine ⟨Z, hZ, ?_⟩
  intro σ I L _ _ _ _ _ _ _ _ _ t d bound D M hs ht p hM V g
  subst ht
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hshift := DilationBudget.shift_bounds q hp
  have hA := DilationBudget.ambient_bounds (s + 1) q hp
  have hQbound := DilationBudget.quotient_bounds (s + 1) q hp
  have hB := DilationBudget.common_bounds (s + 1) q C hp
  obtain ⟨E, hEF, hEL, hE, hdim, he⟩ := M.exists_dilationPair_model (q : ℚ)
    (hM.mono M hshift.2.1) hshift.2.2
  have hE' := hE.mono E hA.2.2.1
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hq, _⟩ := E.exists_controlled_top_quotient hA.1 hE'
  obtain ⟨ε, γ, A, hγ, hfactor, _, hAnorm, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  let K := M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)
  let J := K ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] J)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] J) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] J) := realification_moduleTopology_t2 Q.basis
  have he' (j : Fin 2) (a) (k) : rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection (q : ℚ) j (E.basis a)) k) ≤
        DilationBudget.common (s + 1) q C p := by
    fin_cases j
    · exact (he a k).1.trans (hA.2.2.2.trans hB.2.2.1)
    · exact (he a k).2.trans (hA.2.2.2.trans hB.2.2.1)
  have hall (a : I × (Fin (q ^ (s + 1)).natAbs → I)) := M.exists_prepared_dilation_niltest
    q hs E hEF hEL Q hQF hQL hB.1 (hM.1.mono D hB.2.1) (hE'.mono E hB.2.2.1) he'
    (hQ.mono Q hB.2.2.2.1)
    (fun j k => (hq k j).trans (hQbound.2.2.trans hB.2.2.2.1))
    (V.mono hB.2.1) g ε γ hγ hfactor A (hAnorm.trans (Real.exp_le_exp.mpr hB.2.2.2.2)) hε a.1 a.2
  choose T hnorm hcomplex hzero heval using hall
  refine ⟨{
    L := J
    dim := n
    model := Q
    test := T
    norm := fun a => (hnorm a).le
    complexity := fun a => (hcomplex a).mono (hbudget p hp).1
    normalized := hzero
    eval := heval }, hn.trans hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_dilation_family {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeIntegerModelFamily (fun _ : σ => 1) ((∑ j, bound j) - 1)
        ((p + C) ^ C) (dilationTensorCrossProduct W.eval q (∑ j, bound j)),
        R.dim ≤ 2 * W.dim := by
  obtain ⟨C, hC, hcontrol⟩ := exists_controlled_dilation_family ((∑ j, bound j) - 1) q
  exact ⟨C, hC, fun W => hcontrol W.model W.multi rfl (Nat.sub_add_cancel hpos).symm
    W.complexity W.vertical W.orbit⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_fin_two {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 2 → G) → M) : (𝔼 x, F x) = 𝔼 h : G, 𝔼 n : G, F ![h, n] := by
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro h _
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro n _
  have hc (y : Fin 0 → G) : F (Fin.cons h (Fin.cons n y)) = F ![h, n] := by
    congr 1
    funext k
    fin_cases k <;> rfl
  simp only [hc, Fintype.expect_const]

theorem norm_correlation_partition_bound {X I : Type*} [Fintype X] [Fintype I]
    (f u : X → ℂ) (v : I → X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖𝔼 x, f x * star (u x)‖ ≤
      (∑ i, ‖𝔼 x, f x * star (v i x)‖) + 𝔼 x, ‖u x - ∑ i, v i x‖ := by
  have he := norm_correlation_sub_le_mean f u (fun x => ∑ i, v i x) hf
  have ht := norm_le_norm_add_norm_sub
    (𝔼 x, f x * star (∑ i, v i x)) (𝔼 x, f x * star (u x))
  have hm : (𝔼 x, f x * star (∑ i, v i x)) = ∑ i, 𝔼 x, f x * star (v i x) := by
    simp only [star_sum, Finset.mul_sum, Finset.expect_sum_comm]
  rw [norm_sub_rev] at ht
  have hsum := norm_sum_le (s := Finset.univ) (f := fun i => 𝔼 x, f x * star (v i x))
  rw [hm] at ht he
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicDivision (d : ℕ) {N : ℕ} (x : ZMod N) : ZMod N := (x.val / d : ℕ)

theorem cyclicDivision_val (d : ℕ) {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicDivision d x).val = x.val / d :=
  ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

theorem cyclicDivision_with_residue_injective (d : ℕ) [NeZero d] {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicDivision d x, (x.val : ZMod d))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod d => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod d => z.2.val) h
  simp only [cyclicDivision_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  have hx := Nat.mod_add_div x.val d
  have hy := Nat.mod_add_div y.val d
  rw [hq, hr] at hx
  exact hx.symm.trans hy

theorem expect_cyclicDivision_le (d : ℕ) [NeZero d] {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicDivision d x)) ≤ d * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicDivision d x)) ≤ ∑ z : ZMod N × ZMod d, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicDivision d x, (x.val : ZMod d)))
      (cyclicDivision_with_residue_injective d).injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod d, f z.1) = d * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (d * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem expect_pair_cyclicDivision_le (d : ℕ) [NeZero d] {N : ℕ} [NeZero N]
    (f : (Fin 2 → ZMod N) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicDivision d (x i))) ≤
      (d : ℝ) ^ 2 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicDivision d (![h, n] i)) =
      ![cyclicDivision d h, cyclicDivision d n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, d * (𝔼 n : ZMod N, f ![cyclicDivision d h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicDivision_le d (fun n => f ![cyclicDivision d h, n]) (fun n => hf _)
    _ = d * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicDivision d h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ d * (d * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      exact expect_cyclicDivision_le d (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicHalf {N : ℕ} (x : ZMod N) : ZMod N := (x.val / 2 : ℕ)

theorem cyclicHalf_val {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicHalf x).val = x.val / 2 := by
  exact ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

theorem cyclicHalf_with_parity_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicHalf x, (x.val : ZMod 2))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod 2 => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod 2 => z.2.val) h
  simp only [cyclicHalf_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  omega

theorem expect_cyclicHalf_le {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicHalf x)) ≤ 2 * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicHalf x)) ≤ ∑ z : ZMod N × ZMod 2, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicHalf x, (x.val : ZMod 2)))
      cyclicHalf_with_parity_injective.injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod 2, f z.1) = 2 * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (2 * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem expect_pair_cyclicHalf_le {N : ℕ} [NeZero N] (f : (Fin 2 → ZMod N) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicHalf (x i))) ≤
      4 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicHalf (![h, n] i)) = ![cyclicHalf h, cyclicHalf n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, 2 * (𝔼 n : ZMod N, f ![cyclicHalf h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicHalf_le (fun n => f ![cyclicHalf h, n]) (fun n => hf _)
    _ = 2 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicHalf h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ 2 * (2 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact expect_cyclicHalf_le (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_unit_bounded_vertical_mean_row :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ H X L : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
        U.ComplexityLE ((p + C) ^ C) ∧ U.normBound ≤ 1 ∧ U.orbit = T.orbit ∧
        (∀ i, rationalLogHeight (η (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          U.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star (U.eval (sample h x))‖) := by
  obtain ⟨A, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (2 * X + 2 + Polynomial.C A) ^ A + (2 * X + 2) + 2)
  refine ⟨C, hC, ?_⟩
  intro σ H Y L _ _ _ _ _ _ _ _ _ _ s d D w T p hp hT sample f hf hcorr
  let r := 2 * p + 2
  let δ := Real.exp (-(p + 2))
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδr : δ⁻¹ ≤ Real.exp r := by
    dsimp [δ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by dsimp [r]; linarith)
  obtain ⟨J, inst, η, U, hcard, hheight, hU, hchar, hint, _, _, herr⟩ :=
    T.exists_controlled_vertical_decomposition hr (hT.mono hpr) δ hδ hδr
  let := inst
  have hrow (h : H) : ‖𝔼 x, f h x * star (T.eval (sample h x))‖ ≤
      (∑ j : J, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖) + δ := by
    apply (norm_correlation_partition_bound (f h)
      (fun x => T.eval (sample h x)) (fun j x => (U j).eval (sample h x)) (hf h)).trans
    apply add_le_add le_rfl
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [norm_sub_rev] using herr (sample h x)
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm, Fintype.expect_const] at hm
  have htwo : 2 * δ ≤ Real.exp (-p) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hs : δ ≤ ∑ j : J, (𝔼 h, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖) := by
    linarith
  obtain ⟨j, hj⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ))
    (fun j => 𝔼 h, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖)
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hs)
  have hne : ∃ x, (U j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (U j).eval x = 0 := fun x => hzero _
    simp only [heval, star_zero, mul_zero, Finset.expect_const_zero, norm_zero] at hj
    exact (not_le_of_gt (div_pos hδ (Real.exp_pos _))) hj
  let q := p + verticalDecompositionBudget r + r + 2
  have hq : q ≤ (p + C) ^ C := by
    have hb : p + (r + A) ^ A + r + 2 ≤ (p + C) ^ C := by
      simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
    dsimp [q]
    linarith [hvertical r hr]
  have hrq : r ≤ (p + C) ^ C := by
    have hv := verticalDecompositionBudget_nonneg hr
    dsimp [q] at hq
    linarith
  have hvq : verticalDecompositionBudget r ≤ (p + C) ^ C := by
    dsimp [q] at hq
    linarith
  have hnormcorr : Real.exp (-q) ≤
      (𝔼 h, ‖𝔼 x, f h x * star (((U j).expNormalize r).eval (sample h x))‖) := by
    simp only [expNormalize_eval]
    rw [mean_row_correlation_scale f (fun h x => (U j).eval (sample h x)) (Real.exp_nonneg _)]
    have heq : Real.exp (-r) * (δ / Real.exp (verticalDecompositionBudget r)) =
        Real.exp (-q) := by
      dsimp [δ, q]
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hj (Real.exp_nonneg _)
  refine ⟨η j, (U j).expNormalize r,
    ((U j).expNormalize_complexity (hU j).1).mono hrq,
    (U j).expNormalize_norm (hU j).1, (hU j).2,
    fun i => (hheight j i).trans hvq, ?_, hint j hne,
    (Real.exp_le_exp.mpr (neg_le_neg hq)).trans hnormcorr⟩
  intro z hz x
  change (Real.exp (-r) : ℂ) * (U j).observable (z • x) =
    _ * ((Real.exp (-r) : ℂ) * (U j).observable x)
  rw [hchar j z hz]
  ring

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {σ L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {S : Subgroup D.RealGroup} {p : ℝ} {w : σ → ℕ}

noncomputable def test (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) : D.Niltest w where
  orbit := g
  observable := V.observable i
  normBound := 1
  lipBound := V.lipBound
  norm_le := V.norm i
  lipschitz := V.lipschitz i

theorem test_eval (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) (x : σ → ℤ) :
    (V.test g i).eval x = V.observable i
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) := rfl

theorem test_complexity (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (i : I) : (V.test g i).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  have ht := niltest_log_bound_of_exp (1 : ℝ≥0) V.lipBound (a := 0) (b := p)
    (by norm_num) hp (by simp) V.lip_bound
  simpa only [test, zero_add] using ht

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_unit_vertical_mean_row_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ H X L : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
          (Fin (n + 1)) ((p + C) ^ C),
        D.GeometryComplexityLE ((p + C) ^ C) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) := by
  obtain ⟨A, _, hmode⟩ := Niltest.exists_unit_bounded_vertical_mean_row
  obtain ⟨B, _, hcomplete⟩ := exists_native_unit_vertical_completion s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B + 1)
  refine ⟨C, hC, ?_⟩
  intro σ H Y L _ _ _ _ _ _ _ _ _ _ d D w T p hp hT sample f hf hcorr
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r + 1 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨η, U, hU, hUnorm, horbit, hheight, hchar, hint, hcorrU⟩ :=
    hmode D T hp hT sample f hf hcorr
  obtain ⟨h, x, hx⟩ := exists_large_value_of_mean_row_correlation f
    (fun h x => U.eval (sample h x)) hf hcorrU
  let y : D.Space := QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (sample h x) U.orbit)
  obtain ⟨n, hn, hncard, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvchar⟩ :=
    hcomplete D U hq hU hUnorm η hchar y hx
  let V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
      (Fin (n + 1)) ((p + C) ^ C) :=
    { observable := v
      unit := hvunit
      norm := hvnorm
      lipBound := K
      lip_bound := hK.trans (Real.exp_le_exp.mpr hrC)
      lipschitz := hvLip
      frequency := η
      height := fun i => (hheight i).trans hqC
      vertical := hvchar
      integral := hint }
  have hscalar (z : σ → ℤ) : (V.test T.orbit 0).eval z = U.eval z / 2 := by
    rw [UnitVerticalObservable.test_eval]
    change v 0 _ = U.eval z / 2
    rw [hv0]
    unfold Niltest.eval
    rw [horbit]
  have hmean : (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) =
      (𝔼 h, ‖𝔼 x, f h x * star (U.eval (sample h x))‖) / 2 := by
    simp only [hscalar, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div,
      norm_div]
    norm_num
  refine ⟨n, hn, hncard.trans (Real.exp_le_exp.mpr hrC), V,
    hU.1.mono D hqC, ?_⟩
  rw [hmean]
  have hhalf : Real.exp (-(q + 1)) ≤ Real.exp (-q) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-q)
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (hhalf.trans (div_le_div_of_nonneg_right hcorrU (by norm_num)))

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeMultidegreeNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ τ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def component (i : Fin W.outputDim) : W.model.Niltest (fun _ : σ => 1) where
  orbit := W.multi.orbitToOrdinary W.orbit
  observable := W.vertical.observable i
  normBound := 1
  lipBound := W.vertical.lipBound
  norm_le := W.vertical.norm i
  lipschitz := W.vertical.lipschitz i

theorem component_eval (i : Fin W.outputDim) (x : σ → ℤ) : (W.component i).eval x = W.eval i x := by
  exact congrArg (fun z : W.model.RealGroup => W.vertical.observable i (QuotientGroup.mk z))
    (W.multi.orbitToOrdinary_eval W.orbit x)

theorem component_complexity (i : Fin W.outputDim) : (W.component i).ComplexityLE (p + 4) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  refine ⟨W.complexity.1.mono W.model (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (W.vertical.lipBound : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp p := by linarith [W.vertical.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem exists_linear_niltest [Fintype τ] (i : Fin W.outputDim) (f : σ → ((τ → ℤ) →+ ℤ)) :
    ∃ T : W.model.Niltest (fun _ : τ => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ x, T.eval x = W.eval i (fun j => f j x) := by
  refine ⟨(W.component i).linearPullbackHom f, rfl, W.component_complexity i, ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, W.component_eval]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def antisymmetricKernel {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ℂ :=
  star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)

theorem antisymmetricKernel_norm {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ‖W.antisymmetricKernel i j x y‖ ≤ 1 := by
  rw [antisymmetricKernel, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i _)).trans
    (W.norm_eval j _)

theorem antisymmetricKernel_cyclic {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (N : ℕ) [NeZero N] (i j : Fin W.outputDim) (x y : ZMod N) :
    W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ) =
      star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x) := by
  have he (k : Fin W.outputDim) (x y : ZMod N) :
      W.eval k (correlationInput (x.val : ℤ) (y.val : ℤ)) =
        W.evalCyclic N k (correlationInput x y) := by
    apply congrArg (W.eval k)
    funext l
    fin_cases l <;> rfl
  simp only [antisymmetricKernel, he]

theorem exists_mixed_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (d : Fin 2) (c : ℤ) (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.eval k (Function.update (fun _ => c) d (x ())))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W d c k
  classical
  let A : Fin 2 → ℤ := fun j => if j = d then 1 else 0
  let b : Fin 2 → ℤ := fun j => if j = d then 0 else c
  obtain ⟨E, _⟩ := hfreeze W {d} A b k (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [A, hj])
  have hdegree : (∑ j ∈ ({d} : Finset (Fin 2)), mixedCorrelationDegree 1 j) = 1 := by
    simp only [Finset.sum_singleton]
    fin_cases d <;> rfl
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (Function.update (fun _ => c) d (x ()))) := by
    funext x
    apply congrArg (W.eval k)
    funext j
    by_cases hj : j = d
    · subst j
      simp [A, b]
    · simp [A, b, hj]
  exact ⟨by simpa only [hdegree, heq] using E⟩

theorem exists_antisymmetric_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (d : Fin 2) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => let z := Function.update (fun _ => c) d (x ())
          W.antisymmetricKernel i j (z 0) (z 1))) := by
  obtain ⟨A, _, hslice⟩ := exists_mixed_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hslice W d c i
  obtain ⟨F⟩ := hslice W d.rev c j
  obtain ⟨G⟩ := hmul (by positivity : 0 ≤ (p + A) ^ A) E.conjugate F
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => star (W.eval i (Function.update (fun _ => c) d (x ()))) *
      W.eval j (Function.update (fun _ => c) d.rev (x ()))) =
      (fun x => let z := Function.update (fun _ => c) d (x ())
        W.antisymmetricKernel i j (z 0) (z 1)) := by
    funext x
    unfold antisymmetricKernel
    congr 1
    · congr 1
      apply congrArg (W.eval i)
      funext l
      fin_cases l <;> rfl
    · apply congrArg (W.eval j)
      funext l
      fin_cases d <;> fin_cases l <;> rfl
  exact ⟨by simpa only [heq] using G.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_integer_translation_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ a b : σ → ℤ,
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) (x + a) g)))
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) (x + b) g))) := by
  obtain ⟨A, _, hexpand⟩ := exists_shifted_product_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D p V g hp hD hI a b
  let r := (p + A) ^ A
  let q := r + p + 4
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hrq : r ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hbound : q ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hd := hI.trans (Real.exp_le_exp.mpr (hpq.trans hbound))
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ D.filtration.squareLieSubalgebra)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))
  refine ⟨hd, hd, ?_⟩
  intro i j
  obtain ⟨n, Q, S, _, hSc, hSe⟩ := hexpand D V g hp hD (fun _ => Nat.zero_lt_one) i j a b
  have hcard : (Fintype.card (Fin 4) : ℝ) ≤ Real.exp q := by
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    have h4 : 4 ≤ q := by dsimp [q]; linarith
    linarith [Real.add_one_le_exp q]
  have hcost : (∑ k, ‖polarizationWeight k‖) ≤ Real.exp q := by
    rw [polarizationWeight_cost]
    exact Real.one_le_exp hq
  exact ⟨(NativeIntegerExpansion.ofFamily Q S polarizationWeight hcard
    (fun k => (hSc k).mono hrq) hcost hSe).mono hbound⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_multidegree_integer_translation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (a b : σ → ℤ), NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ := UnitVerticalObservable.exists_integer_translation_equivalence_budget s
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W a b
  rw [← hdegree] at htranslate
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let U : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ i, bound i)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model U (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hI a b
  have heval (i : Fin W.outputDim) (x : σ → ℤ) :
      U.observable i (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (W.multi.orbitToOrdinary W.orbit))) = W.eval i x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  simpa only [heval] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (F : D.AdaptedModelData) (H : ℕ)
  (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) {w : σ → ℕ}

noncomputable def rebaseNiltest (T : D.Niltest w) : F.model.Niltest w where
  orbit := T.orbit
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d (finrank ℚ L) H
  norm_le := T.norm_le
  lipschitz := by
    let := F.model.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hT : dist (T.observable x) (T.observable y) ≤
        (T.lipBound : ℝ) * @dist D.Space D.metricSpace.toDist x y := by
      let := D.metricSpace
      exact T.lipschitz.dist_le_mul x y
    calc
      dist (T.observable x) (T.observable y) ≤
          (T.lipBound : ℝ) * @dist D.Space D.metricSpace.toDist x y := hT
      _ ≤ (T.lipBound : ℝ) *
          (coordinateLipschitzBound d (finrank ℚ L) H * dist x y) :=
        mul_le_mul_of_nonneg_left (F.original_dist_le H hH x y) T.lipBound.coe_nonneg
      _ = ↑(T.lipBound * coordinateLipschitzBound d (finrank ℚ L) H) * dist x y := by
        rw [NNReal.coe_mul]
        ring

theorem rebaseNiltest_complexity (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hT : T.ComplexityLE p) (hF : F.model.GeometryComplexityLE p) (hHp : (H : ℝ) ≤ Real.exp p) :
    (F.rebaseNiltest H hH T).ComplexityLE (p + (p + 2) ^ 2) := by
  have hK : (coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    coordinateLipschitzBound_le_exp d (finrank ℚ L) H hp hT.1.1 hF.1 hHp
  have h1 : 1 ≤ Real.exp ((p + 2) ^ 2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  refine ⟨hF.mono F.model (le_add_of_nonneg_right (sq_nonneg _)), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * coordinateLipschitzBound d (finrank ℚ L) H) ≤ p + (p + 2) ^ 2
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * coordinateLipschitzBound d (finrank ℚ L) H ≤
        (2 + (T.normBound : ℝ)) * Real.exp ((p + 2) ^ 2) +
          (T.lipBound : ℝ) * Real.exp ((p + 2) ^ 2) :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hK T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp ((p + 2) ^ 2) := by ring
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (Niltest.observable_budget hT) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 2) := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

end

section

namespace Erdos3

def rankAdaptedNiltestBase (p : ℝ) : ℝ := (p + 3) ^ 11 + p + 2

def rankAdaptedNiltestBudget (p : ℝ) : ℝ :=
  rankAdaptedNiltestBase p + (rankAdaptedNiltestBase p + 2) ^ 2

theorem le_rankAdaptedNiltestBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ rankAdaptedNiltestBudget p := by
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  unfold rankAdaptedNiltestBudget rankAdaptedNiltestBase
  nlinarith [sq_nonneg ((p + 3) ^ 11 + p + 2 + 2)]

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

theorem exists_adapted_niltest {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)
    {w : σ → ℕ} (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hR : R.ComplexityLE p) (hT : T.ComplexityLE p) :
    ∃ F : R.AdaptedData,
      F.rank.ComplexityLE (rankAdaptedNiltestBudget p) ∧
      (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1) ∧
      (∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + 3) ^ 5) ∧
      ∃ S : F.model.Niltest w, S.orbit = T.orbit ∧ S.observable = T.observable ∧
        S.ComplexityLE (rankAdaptedNiltestBudget p) := by
  obtain ⟨F, hF, hb, hinv⟩ := R.exists_rank_adapted_data hp hR
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let q := rankAdaptedNiltestBase p
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpq : p ≤ q := by dsimp [q, rankAdaptedNiltestBase]; linarith
  have hfq : (p + 3) ^ 11 ≤ q := by dsimp [q, rankAdaptedNiltestBase]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [q, rankAdaptedNiltestBase]; linarith))
  have hqb : q ≤ rankAdaptedNiltestBudget p := by
    exact le_add_of_nonneg_right (sq_nonneg _)
  refine ⟨F, hF.mono F.rank (hfq.trans hqb), hb, hinv,
    F.toAdaptedModelData.rebaseNiltest H hH T, rfl, rfl, ?_⟩
  exact F.toAdaptedModelData.rebaseNiltest_complexity H hH T hq
    (hT.mono hpq) (hF.1.mono F.model hfq) hHq

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_residue_class_right_lattice_factors {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : (σ → ℤ) → G) (M : ℕ) (P : G → Prop)
    (hperiod : ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
      (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (f y))
    (hrep : ∀ x : σ → ℤ, ∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = r * γ) :
    ∃ r : (σ → ZMod M) → G,
      (∀ c, P (r c)) ∧
      ∀ x : σ → ℤ, ∃ γ ∈ Γ,
        f x = r (fun j => (x j : ZMod M)) * γ := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ :=
    fun c j => Classical.choose (ZMod.intCast_surjective (c j))
  have hlift (c : σ → ZMod M) (j : σ) : (lift c j : ZMod M) = c j :=
    Classical.choose_spec (ZMod.intCast_surjective (c j))
  choose r hr γ hγ heq using fun c => hrep (lift c)
  refine ⟨r, hr, ?_⟩
  intro x
  let c := fun j => (x j : ZMod M)
  have hxy (j : σ) : (M : ℤ) ∣ x j - lift c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (lift c j) (x j) M).mp (hlift c j)
  have hR : (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (r c) := by
    apply (hperiod x (lift c) hxy).trans
    rw [heq c]
    exact QuotientGroup.mk_mul_of_mem _ (hγ c)
  refine ⟨(r c)⁻¹ * f x, QuotientGroup.eq.mp hR.symm, ?_⟩
  change f x = r c * ((r c)⁻¹ * f x)
  group

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_kernel_residue_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
      (w : σ → ℕ), (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M m : ℕ, 0 < M ∧ 0 < m ∧
        (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          (∀ x : σ → ℤ, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ
            (D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g) = 1) →
          ∃ r : (σ → ZMod M) → D.RealGroup,
            (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := F.lowerCentralSeries_eq_bot) φ (r a) = 1 ∧
              (∀ i, |(D.basis.baseChange ℝ).repr (r a).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (r a).coord ∈ realDenominatorGrid m) ∧
            ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                r (fun j => (x j : ZMod M)) * γ := by
  obtain ⟨a, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨b, _, hrep⟩ := exists_native_marked_kernel_representatives s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c φ w hw p hp hD hσ hκ hφ q hq hqp
  obtain ⟨M, hM, hMb, hper⟩ := hperiod D w hw p hp hD hσ q hq hqp
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D c φ p hp hD hκ hφ q hq hqp
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (p + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)).trans hsum
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr haC),
    hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg hmark
  let f := fun x : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g
  let A := fun r : D.RealGroup =>
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ r = 1 ∧
    (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m
  have hf (x : σ → ℤ) : ∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = r * γ := by
    have hxK := (mem_realificationSubgroup_ker_iff
      (hM := F.lowerCentralSeries_eq_bot) φ (f x)).mpr (hmark x)
    obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps (f x) hxK
      (D.filtration.polynomialRationalGrid_value D.basis w q g hg x)
    refine ⟨r, ⟨?_, fun i => (hr i).trans (Real.exp_le_exp.mpr hbC), hrgrid⟩, γ, hγ, hfac⟩
    exact (mem_realificationSubgroup_ker_iff (hM := F.lowerCentralSeries_eq_bot) φ r).mp hrK
  obtain ⟨r, hr, hfac⟩ := exists_residue_class_right_lattice_factors D.realLattice f M A
    (fun x y hxy => (hper g hg x y hxy).1) hf
  exact ⟨r, hr, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredResidueExpansionSpec
    (p : ℝ) (q r P : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
        (Fintype.card (Σ i : I₀, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      letI := Z.metricSpace
      let w := fun _ : Unit => 1
      let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
      let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
      ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (freq j)) x = 0) →
        ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
          (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ η : ℝ},
          0 < ρ → 0 ≤ η →
          (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
          (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
          (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
          (∀ i x y, 0 < A i x → 0 < A i y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
          ∀ (S : ZMod N → (D a).Niltest w),
            (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
            (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (freq j a) z.coord = 0) →
              ∀ x, (S h).observable (z • x) = (S h).observable x) →
            ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
              (κ : ZMod N → (D a).RealGroup)
              (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
              (∀ h, κ h ∈ (D a).realLattice) →
              (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
              (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
              (∀ h, (D a).filtration.PolynomialRationalGrid (D a).basis w q (rat h)) →
              (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
              (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                  (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
                  (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                    (fun _ => (y.val : ℤ)) (g h)))) ≤ η) →
              ∃ U : I → J → ZMod N → Q'.Niltest w,
                (∀ i j h, (U i j h).UnitIntervalValued) ∧
                (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                  ∀ x, (U i j h).eval x = 0) ∧
                ∃ err : ZMod N → ZMod N → ℝ,
                  (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                    (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                  ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (ρ + η) + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold
namespace OAI

section

namespace Erdos3

theorem scaledIntegerGrid_le_denominatorGrid {ι : Type*} (a b : ℕ) :
    (scaledIntegerGrid a : Set (ι → ℚ)) ⊆ denominatorGrid b := by
  rintro x ⟨z, rfl⟩
  exact ((show IntegralVector (fun i => (z i : ℚ)) from ⟨z, fun _ => rfl⟩).nat_smul a).nat_smul b

namespace DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L)
  (htail : ∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c)

noncomputable def tailLayerBasis (i j : ℕ) :
    Basis (Fin (finrank ℚ (F.layer i j))) ℚ (F.layer i j) :=
  basisOfTail b (F.layer i j) (Classical.choose (htail i j)) (Classical.choose_spec (htail i j)).2

theorem tailLayerBasis_height (i j : ℕ) (a : Fin (finrank ℚ (F.layer i j))) (k : Fin d) :
    RationalHeightLE (b.repr (F.tailLayerBasis b htail i j a : L) k) 1 :=
  basisOfTail_height b (F.layer i j) (Classical.choose (htail i j)) (Classical.choose_spec (htail i j)).2 a k

variable (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule b B, ∀ y ∈ coordinateGridModule b B,
    lieBCH s x y ∈ coordinateGridModule b B)

noncomputable def integralGridNilmanifold : RationalFilteredNilmanifold L s d where
  filtration := F.associatedDegree
  basis := b
  layerBasis i := F.tailLayerBasis b htail (i.val + 1) 0
  lattice := coordinateGridBCHSubgroup b B F.associatedDegree.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def integralGridDegreeRank :
    (F.integralGridNilmanifold b htail B hB hstable).DegreeRankStructure r where
  filtration := F
  associated := rfl
  basis i j := F.tailLayerBasis b htail i.val j.val

theorem integralGridNilmanifold_coordinates :
    bchSubgroupCoordinates (F.integralGridNilmanifold b htail B hB hstable).basis
      (F.integralGridNilmanifold b htail B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates b B F.associatedDegree.lowerCentralSeries_eq_bot hstable

theorem integralGridDegreeRank_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hgrid : (B : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.integralGridDegreeRank b htail B hB hstable).ComplexityLE p := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp p := by
    simpa only [Nat.cast_one, Real.exp_zero] using Real.exp_le_exp.mpr hp
  refine ⟨⟨hd, hgrid, hc, ?_⟩, ?_⟩
  · intro i a k
    exact rationalLogHeight_le_of_height (F.tailLayerBasis_height b htail (i.val + 1) 0 a k) hone
  · intro i j a k
    exact rationalLogHeight_le_of_height (F.tailLayerBasis_height b htail i.val j.val a k) hone

end DegreeRankLieFiltration

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_controlled_nilmanifold_of_tails (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L : Type*) [LieRing L] [LieAlgebra ℚ L] (r d : ℕ)
      (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L),
      (∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c) →
      ∀ (l : ℕ), 0 < l → ∀ (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      p ≤ (p + C) ^ C ∧ ∃ D : RationalFilteredNilmanifold L s d,
        ∃ R : D.DegreeRankStructure r, D.basis = b ∧ R.filtration = F ∧
          l ∣ D.grid ∧ bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          R.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨C, hC, hgrid⟩ := exists_controlled_integral_grid s
  refine ⟨C, hC, ?_⟩
  intro L _ _ r d F b htail l hl p hp hd hlp hc
  obtain ⟨hpC, B, hB, hdiv, hBbound, hstable⟩ := hgrid L (Fin d) b
    F.associatedDegree.lowerCentralSeries_eq_bot l hl p hp
    (by simpa only [Fintype.card_fin] using hd) hlp hc
  refine ⟨hpC, F.integralGridNilmanifold b htail B hB hstable,
    F.integralGridDegreeRank b htail B hB hstable, rfl, rfl, hdiv,
    F.integralGridNilmanifold_coordinates b htail B hB hstable, ?_⟩
  exact F.integralGridDegreeRank_complexity b htail B hB hstable
    (hp.trans hpC) (hd.trans hpC) hBbound (fun i j k => (hc i j k).trans hpC)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_free_degree_rank_nilmanifold (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (l : ℕ), 0 < l →
      ∀ (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → (l : ℝ) ≤ Real.exp p →
      ∃ D : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ R : D.DegreeRankStructure r,
          R.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          R.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis D.basis ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
            rationalLogHeight (D.basis.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
          ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
            (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
            (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
            ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
                (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
              LinearMap.toMatrix e D.basis (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
              ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hfree⟩ := exists_adapted_free_degree_rank_model s
  obtain ⟨c, _, hnative⟩ := exists_controlled_nilmanifold_of_tails s
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw l hl p hp hX hlp
  let B := (p + a) ^ a
  let T := p + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBT : B ≤ T := le_add_of_nonneg_left hp
  have hpT : p ≤ T := le_add_of_nonneg_right hB
  have hT : 0 ≤ T := hp.trans hpT
  have hsum : T + (T + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, T, B, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + c) ^ c)).trans hsum
  have hNC : (T + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  obtain ⟨hdim, b, hcentral, htail, hstructure, htree, e, he, hdim₀, S, hS, hSH⟩ :=
    hfree X r hr w hw p hp hX
  obtain ⟨_, D, R, hb, hR, hdiv, hcoords, hcomplexity⟩ :=
    hnative (FreeDegreeRankLieAlgebra X s r w hw) r _
      (FreeDegreeRankLieAlgebra.filtration X s r w hw hr) b htail l hl T hT
      (hdim.trans hBT) (hlp.trans (Real.exp_le_exp.mpr hpT))
      (fun i j k => (hstructure i j k).trans hBT)
  refine ⟨D, R, hR, hcomplexity.mono R hNC, ?_, hdiv, hcoords, ?_, e, he,
    hdim₀.trans (hBT.trans hTC), S, ?_, fun i j => (hSH i j).trans (hBT.trans hTC)⟩
  · rw [hb]
    exact hcentral
  · intro x hx i
    rw [hb]
    exact (htree x hx i).trans (hBT.trans hTC)
  · rw [hb]
    exact hS

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

noncomputable def dropTopMap : (D.dropTop hD).Space → D.Space :=
  cosetMap (D.dropTop hD).realLattice D.realLattice
    (realificationMap (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L) (D.dropTop hD).lattice D.lattice
      (D.dropTop_lattice_back hD))

theorem dropTopMap_mk (x : (D.dropTop hD).RealGroup) :
    D.dropTopMap hD (QuotientGroup.mk x) =
      QuotientGroup.mk (changeStep (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot
        D.filtration.realification.lowerCentralSeries_eq_bot x) := by
  change QuotientGroup.mk (realificationMap
    (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) = _
  rw [realificationMap_id_eq_changeStep]

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem dropTopMap_lipschitz :
    letI := (D.dropTop hD).metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (D.dropTopMap hD) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1
      (realificationMap (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
    rw [realificationMap_id_eq_changeStep]
    exact lipschitz_changeStep (D.basis.baseChange ℝ) _ _
  exact lipschitz_cosetMap (D.dropTop hD).realLattice D.realLattice
    (D.dropTop hD).realLattice_closed_discrete.1 D.realLattice_closed_discrete.1 _ _ hLip

end Metric

noncomputable def dropTopRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.dropTop hD).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

theorem dropTopMap_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.dropTopMap hD (QuotientGroup.mk
      ((D.dropTop hD).filtration.realification.polynomialOrbitEval w x (D.dropTopRealOrbit hD g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.dropTopMap_mk]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L (s + 1) d} {w : σ → ℕ}

noncomputable def dropTop (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥) :
    (D.dropTop hD).Niltest w where
  orbit := D.dropTopRealOrbit hD T.orbit
  observable := T.observable ∘ D.dropTopMap hD
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := (D.dropTop hD).metricSpace
    simpa only [mul_one] using T.lipschitz.comp (D.dropTopMap_lipschitz hD)

theorem dropTop_eval (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥) (x : σ → ℤ) :
    (T.dropTop hD).eval x = T.eval x :=
  congrArg T.observable (D.dropTopMap_orbit hD T.orbit x)

theorem dropTop_complexity (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.dropTop hD).ComplexityLE p :=
  ⟨D.dropTop_geometry hD hT.1, hT.2⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NativeDegreeRankFamily

open scoped NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def component (i : Fin W.outputDim) (a : A) :
    W.model.Niltest (fun _ : Unit => 1) where
  orbit := W.orbit a
  observable := W.vertical.observable i
  normBound := 1
  lipBound := W.vertical.lipBound
  norm_le := W.vertical.norm i
  lipschitz := W.vertical.lipschitz i

theorem component_eval (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.component i a).eval (fun _ => n) = W.eval i a n := rfl

theorem component_complexity (hp : 0 ≤ p) (i : Fin W.outputDim) (a : A) :
    (W.component i a).ComplexityLE (p + 4) := by
  refine ⟨W.complexity.1.mono W.model (by linarith), ?_⟩
  have h := niltest_log_bound_of_exp (1 : ℝ≥0) W.vertical.lipBound
    (a := 0) (b := p) (by norm_num) hp (by simp) W.vertical.lip_bound
  simpa only [component, zero_add] using h

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3.NativeDegreeRankFamily

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily (s + 1) 0 A p)

theorem rankZero_top_eq_bot : W.model.filtration.layer (s + 1) = ⊥ := by
  rw [← W.rank.associated]
  exact W.rank.filtration.rank_zero_top_eq_bot

noncomputable def lowerComponent (i : Fin W.outputDim) (a : A) :
    (W.model.dropTop W.rankZero_top_eq_bot).Niltest (fun _ : Unit => 1) :=
  (W.component i a).dropTop W.rankZero_top_eq_bot

theorem lowerComponent_eval (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.lowerComponent i a).eval (fun _ => n) = W.eval i a n := by
  rw [lowerComponent, RationalFilteredNilmanifold.Niltest.dropTop_eval, W.component_eval]

theorem lowerComponent_evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) :
    (W.lowerComponent i a).evalCyclic N (fun _ => n) = W.evalCyclic N i a n :=
  W.lowerComponent_eval i a _

theorem lowerComponent_complexity (hp : 0 ≤ p) (i : Fin W.outputDim) (a : A) :
    (W.lowerComponent i a).ComplexityLE (p + 4) :=
  (W.component i a).dropTop_complexity W.rankZero_top_eq_bot (W.component_complexity hp i a)

end Erdos3.NativeDegreeRankFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]

theorem exists_rankInvariant_niltest
    (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientLie
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal)
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z ∈ R.realSubgroup s (r + 1), ∀ x, T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr
      (lieQuotientMap (R.filtration.layerIdeal s (r + 1)) (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = R.rankQuotientOrbit Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound ∧
      (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
        T.observable (QuotientGroup.mk x)) ∧
      ∀ x, S.eval x = T.eval x := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))
    (lieQuotientMap_surjective _) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff
        (R.filtration.layerIdeal s (r + 1)).toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := R.rankQuotientOrbit Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  }
  refine ⟨S, rfl, rfl, rfl, hf, ?_⟩
  intro x
  exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
    (R.rankQuotientOrbit_eval Q hQF T.orbit x)).trans (hf _)

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open scoped TensorProduct NNReal

theorem exists_rankInvariant_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d n : ℕ} {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [T2Space (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
      (hQF : Q.filtration = D.filtration.quotientLie
        (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal)
      (_hQL : Q.lattice = D.lattice.map
        (D.filtration.quotientStepHom (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1)) (D.basis j)) i) ≤ p) →
      (∀ z ∈ R.realSubgroup s (r + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = R.rankQuotientOrbit Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
        (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
          (NilpotentLieBCHGroup.realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
          T.observable (QuotientGroup.mk x)) ∧
        ∀ x, S.eval x = T.eval x := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 1 + Polynomial.C a) ^ a + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ r d n D R _ _ _ _ Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hSp, hSe⟩ := R.exists_rankInvariant_niltest Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + C) ^ C := by
    simpa [r, P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩, hSp, hSe⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

end


