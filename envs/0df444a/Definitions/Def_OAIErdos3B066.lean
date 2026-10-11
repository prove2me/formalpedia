-- Prove2me | Definitions.Def_OAIErdos3B066
-- name    : OAIErdos3B066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T16:49:25.861984+00:00
-- url     : https://prove2.me/theorems/a8218097-7398-436c-977e-26dce8826c84
-- title:
--   OpenAI Erdős-3 split, definitions bundle 67 of 210
-- statement:
--   Definitions bundle 67 of 210 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B065`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 67 available.
--
--   Modules: `OAI.Erdos3.NativeAntisymmetricPairFactorization`, `OAI.Erdos3.NativeAntisymmetricPairFactorization.mono`, `OAI.Erdos3.NativeMultidegreeNilcharacter.pairComponentPolynomial`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasPairFrozenEquivalence`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasPairFrozenReduction`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasPairLocalApproximation`, `OAI.Erdos3.NativePolynomialOrbitFactors.hasPairFrozenEquivalence_mono`, `OAI.Erdos3.NativePolynomialOrbitFactors.hasPairFrozenReduction_mono`, `OAI.Erdos3.NativePolynomialOrbitFactors.hasPairLocalApproximation_mono`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairAnchoredVector`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairAnchoredVector_norm`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairCoordinate_common_vertical`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairCoordinate_comparison_invariant`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairFrozenEquivalence_at`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairFrozenVector`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairFrozenVector_diagonal`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairFrozenVector_error`, `OAI.Erdos3.NativePolynomialOrbitFactors.pairFrozenVector_unit`, `OAI.Erdos3.NativePolynomialOrbitFactors.pair_comparison_invariant`, `OAI.Erdos3.NativePolynomialOrbitFactors.pair_eval_component`, `OAI.Erdos3.NativePolynomialOrbitFactors.pair_projected_product`, `OAI.Erdos3.NativePolynomialOrbitFactors.pair_top_agreement`, `OAI.Erdos3.NativePolynomialOrbitFactors.select_pair_local_partition`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairFrequency_apply`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairFrequency_real`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairNiltest_symbol`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairPolynomial`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairPolynomialMap`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairPolynomialMap_constant`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairPolynomialMap_eq`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairPolynomialMap_value`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairProjection`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairProjection_lattice`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairProjection_layers`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonNiltest`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonNiltest_complexity`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonNiltest_observable`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonNiltest_vertical`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonTests`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonTests_complexity`, `OAI.Erdos3.NativeSampleCorrelation.pairComparisonTests_vertical`, `OAI.Erdos3.PolynomialTranslationLie.card_le_weightedBasisIndex`, `OAI.Erdos3.PolynomialTranslationLie.exists_translationMajorDetectedPotentialData`, `OAI.Erdos3.PolynomialTranslationLie.exists_translation_major_correlation_step_drop`, `OAI.Erdos3.PolynomialTranslationLie.exists_translation_major_twisted_correlation_step_drop`, `OAI.Erdos3.PolynomialTranslationLie.exists_translation_major_vertical_selection`, `OAI.Erdos3.PolynomialTranslationLie.pairTranslationProjection_coordinate_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueNilmanifold_base_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.PairAlgebra`, `OAI.Erdos3.RationalFilteredNilmanifold.finrank_eq_dimension`, `OAI.Erdos3.RationalFilteredNilmanifold.geometry_finrank_le`, `OAI.Erdos3.RationalFilteredNilmanifold.geometry_pair_finrank_le`, `OAI.Erdos3.RationalFilteredNilmanifold.geometry_pair_finrank_le_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.pairFirstProjection_filtered`, `OAI.Erdos3.RationalFilteredNilmanifold.pairFrequencies`, `OAI.Erdos3.RationalFilteredNilmanifold.pairFrequency`, `OAI.Erdos3.RationalFilteredNilmanifold.pairFrequency_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.pairFrequency_zero_comp`, `OAI.Erdos3.RationalFilteredNilmanifold.pairModels`, `OAI.Erdos3.RationalFilteredNilmanifold.pairNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.pairNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.pairNiltest_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.pairNiltest_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.pairNiltest_symbol`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_first_projection`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbit_first_projection_log`, `OAI.Erdos3.RationalFilteredNilmanifold.pairTests`, `OAI.Erdos3.RationalFilteredNilmanifold.pairTests_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_coordinate_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_repr`, `OAI.Erdos3.exists_antisymmetric_anchor_equivalence`, `OAI.Erdos3.exists_antisymmetric_pair_frozen_equivalence`, `OAI.Erdos3.exists_antisymmetric_pair_frozen_reduction`, `OAI.Erdos3.exists_antisymmetric_pair_local_approximation`, `OAI.Erdos3.exists_antisymmetric_pair_local_partition`, `OAI.Erdos3.exists_antisymmetric_pair_orbit_factors`, `OAI.Erdos3.exists_antisymmetric_pair_outer_control`, `OAI.Erdos3.exists_antisymmetric_pair_step_drop`, `OAI.Erdos3.exists_finite_product_vertical_step_drop`, `OAI.Erdos3.exists_intrinsic_step_drop`, `OAI.Erdos3.exists_native_pair_positive_step_drop`, `OAI.Erdos3.exists_native_pair_vertical_step_drop`, `OAI.Erdos3.exists_quadratic_pair_step_drop`, `OAI.Erdos3.mixedCyclicErrorBuffer`, `OAI.Erdos3.mixedCyclicErrorSlope`, `OAI.Erdos3.mixed_cyclic_error_bound`, `OAI.Erdos3.pairFrequency_logHeight`, `OAI.Erdos3.two_mul_le_translation_major_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B201

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MixedCyclicErrorBudget
namespace OAI

section

namespace Erdos3

def mixedCyclicErrorSlope (s : ℕ) : ℕ := mixedRootTensorExponent s + mixedRootCornerExponent s

def mixedCyclicErrorBuffer (s : ℕ) : ℕ := 2 * mixedRootCornerCoefficient s + 14

theorem mixed_cyclic_error_bound (s : ℕ) {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + mixedCyclicErrorBuffer s) ≤ N) :
    (d ^ mixedRootTensorExponent s + 1) *
        ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s *
          Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s))) +
      12 * Real.exp (-(e + mixedCyclicErrorBuffer s)) + 2 / N ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have hn : d ^ mixedRootTensorExponent s + 1 ≤
      2 * Real.exp ((mixedRootTensorExponent s : ℝ) * u) := by
    have h := hp (mixedRootTensorExponent s)
    linarith [Real.one_le_exp (show 0 ≤ (mixedRootTensorExponent s : ℝ) * u by positivity)]
  have hcoef : (d ^ mixedRootTensorExponent s + 1) *
      ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s) ≤
      (2 * mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedCyclicErrorSlope s : ℝ) * u) := by
    calc
      _ ≤ (2 * Real.exp ((mixedRootTensorExponent s : ℝ) * u)) *
          ((mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedRootCornerExponent s : ℝ) * u)) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (hp (mixedRootCornerExponent s)) (Nat.cast_nonneg _))
          (by positivity) (by positivity)
      _ = (2 * mixedRootCornerCoefficient s : ℝ) *
          Real.exp ((mixedRootTensorExponent s : ℝ) * u + (mixedRootCornerExponent s : ℝ) * u) := by
        rw [Real.exp_add]
        ring
      _ = _ := by simp only [mixedCyclicErrorSlope, Nat.cast_add, add_mul]
  have hfirst : (d ^ mixedRootTensorExponent s + 1) *
      ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s *
        Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s))) ≤
      (2 * mixedRootCornerCoefficient s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    calc
      _ = ((d ^ mixedRootTensorExponent s + 1) *
          ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s)) *
            Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s)) := by ring
      _ ≤ ((2 * mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedCyclicErrorSlope s : ℝ) * u)) *
          Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using h
  have hthird : 2 / N ≤ 2 * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    calc
      _ = 2 * (1 / N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  calc
    _ ≤ (mixedCyclicErrorBuffer s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
      have h := add_le_add (add_le_add hfirst (le_refl (12 * Real.exp (-(e + mixedCyclicErrorBuffer s))))) hthird
      apply h.trans_eq
      have hB : (mixedCyclicErrorBuffer s : ℝ) = 2 * mixedRootCornerCoefficient s + 14 := by
        simp only [mixedCyclicErrorBuffer, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hB]
      ring
    _ ≤ Real.exp (mixedCyclicErrorBuffer s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (mixedCyclicErrorBuffer s : ℝ)])
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AntisymmetricPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def antisymmetricPairPolynomial :
    ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.antisymmetricPairModels k).filtration)
    (fun k => (V.antisymmetricPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

def antisymmetricPairProjection (k : Fin 2) : V.AntisymmetricPairAlgebra →ₗ⁅ℚ⁆ W.L :=
  liePiEval (some k)

theorem antisymmetricPairFrequency_apply (x : V.AntisymmetricPairAlgebra) :
    piFrequency V.antisymmetricPairFrequencies x =
      W.vertical.frequency (V.antisymmetricPairProjection 1 x) -
        W.vertical.frequency (V.antisymmetricPairProjection 0 x) := by
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  change 0 + (-W.vertical.frequency (x (some 0)) + W.vertical.frequency (x (some 1))) =
    W.vertical.frequency (x (some 1)) - W.vertical.frequency (x (some 0))
  ring

theorem antisymmetricPairFrequency_real (x : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :
    realifyFunctional (piFrequency V.antisymmetricPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul scalar element =>
    simp only [realifyFunctional_tmul, V.antisymmetricPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add left right hleft hright => simp only [map_add, hleft, hright]; ring

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem antisymmetricPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.AntisymmetricPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.antisymmetricPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.antisymmetricPairNiltest.symbol b w hF =
      (pi V.antisymmetricPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin 2 => 1) V.antisymmetricPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_intrinsic_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
      ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (e '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
        ∀ η : L →ₗ[ℚ] ℚ,
          (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
            T.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
          D.filtration.ControlledSymbolFactorization e ω hF η (fun i => (lengths i : ℝ))
            (T.symbol e ω hF) ((p + C) ^ C) := by
  cases s with
  | zero => omega
  | succ s =>
    have hs' : 1 ≤ s := by omega
    obtain ⟨c, _, hI⟩ := exists_translated_step_drop s hs'
    obtain ⟨C, hC, hstep⟩ := exists_biased_chosen_basis_step_drop s c hI
    refine ⟨C, hC, ?_⟩
    intro σ L _ _ _ _ d _ _ _ _ D p hp T hT
    obtain ⟨a, v, _grid, _hv, _central, hA, _rest⟩ := D.exists_controlled_adapted_basis hp hT.1
    obtain ⟨τS, hSA, hSM, hST⟩ := exists_real_module_topology
      (D.filtration.squareFinBasis a v (hA 2))
    let : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := τS
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSA
    let : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSM
    let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hST
    obtain ⟨τQ, hQA, hQM, hQT⟩ := exists_real_module_topology
      (D.filtration.reducedSquareBasis a v hA)
    let : TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := τQ
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQA
    let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQM
    let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQT
    obtain ⟨e, ω, hF, _N, _hN, _hin, _hout, he, _geometry, hconstruct⟩ :=
      hstep hs' D p hp T hT
    obtain ⟨g, hg⟩ := D.filtration.nativePolynomialOrbit_surjective
      (fun _ : σ => 1) e ω hF T.orbit
    refine ⟨e, ω, hF, he, ?_⟩
    intro η hvert origin lengths hlengths hσ hlarge hbias
    have hresult := hconstruct g hg η hvert origin lengths hlengths hσ hlarge hbias
    rw [← T.symbol_of_native e ω hF g hg] at hresult
    exact hresult

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

structure NativeAntisymmetricPairFactorization {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.AntisymmetricPairAlgebra)) ℚ V.AntisymmetricPairAlgebra
  weight : Fin (finrank ℚ V.AntisymmetricPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.antisymmetricPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.antisymmetricPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.antisymmetricPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
    (V.antisymmetricPairNiltest.symbol basis weight adapted) r

noncomputable def NativeAntisymmetricPairFactorization.mono {p q r r' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
    (F : NativeAntisymmetricPairFactorization V r) (hrr' : r ≤ r') :
    NativeAntisymmetricPairFactorization V r' := by
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  exact { F with
    height := fun a b => (F.height a b).trans hrr'
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.antisymmetricPairModels).filtration F.basis F.weight F.adapted F.factorization hrr'
      (fun _ => by exact_mod_cast NeZero.pos N) }

theorem exists_antisymmetric_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeAntisymmetricPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ k, mixedCorrelationDegree 1 k)
    (by decide)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + (X + 2) ^ 2 + 3) + 4
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (antisymmetricPairBudget p q) + (p + q) + 2
  have hprod : 0 ≤ productNiltestBudget (antisymmetricPairBudget p q) := by
    have hbase := V.antisymmetricPairBudget_four_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have h2r : 2 ≤ r := by dsimp [r]; linarith
  have hTr : productNiltestBudget (antisymmetricPairBudget p q) ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, antisymmetricPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.antisymmetricPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htT
  let D := pi V.antisymmetricPairModels
  let T := V.antisymmetricPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.antisymmetricPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 2 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 2 => N) = integerBox (fun _ : Fin 2 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.antisymmetricPairNiltest_bias
  have hf := hconstruct (piFrequency V.antisymmetricPairFrequencies)
    V.antisymmetricPairNiltest_vertical 0 (fun _ : Fin 2 => N)
    (fun _ => NeZero.pos N) (by simpa using h2r)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun a b => (he a b).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3
open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_finite_product_vertical_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (T : ∀ i, (D i).Niltest (fun _ : σ => 1)) {p : ℝ} (hp : 0 ≤ p)
      (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (∀ i, L i))) ℚ (∀ i, L i))
        (ω : Fin (finrank ℚ (∀ i, L i)) → ℕ)
        (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi D).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ eta : ∀ i, L i →ₗ[ℚ] ℚ,
          (∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
            (T i).observable (z • x) = CircleFourier.character
              ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
                (T i).observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, ∏ i, (T i).eval x‖ →
          (pi D).filtration.ControlledSymbolFactorization b ω hF (piFrequency eta)
            (fun i => (lengths i : ℝ)) ((piNiltest D T hp hι hT).symbol b ω hF)
            ((p + C) ^ C) := by
  obtain ⟨a, _ha, hstep⟩ := exists_intrinsic_step_drop s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + 1 + (Q + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D T p hp hι hT
  let q := productNiltestBudget p + p + 2
  have hprod : 0 ≤ productNiltestBudget p := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hTq : productNiltestBudget p ≤ q := by dsimp [q]; linarith
  have hcost : q + 1 + (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hheight : q + 1 ≤ (p + C) ^ C := by
    have : 0 ≤ (q + a) ^ a := by positivity
    linarith
  have hfactor : (q + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (pi D) hq (piNiltest D T hp hι hT)
      ((piNiltest_complexity D T hp hι hT).mono hTq)
  refine ⟨b, ω, hF, fun i j => (hb i j).trans hheight, ?_⟩
  intro eta hvert origin lengths hlength hσ hlarge hbias
  have hpair : Real.exp (-q) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths, (piNiltest D T hp hι hT).eval x‖ := by
    simp_rw [piNiltest_eval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
  have hf := hconstruct (piFrequency eta) (piNiltest_vertical D T eta hp hι hT hvert)
    origin lengths hlength (hσ.trans hpq)
    (fun i => (Real.exp_le_exp.mpr hfactor).trans (hlarge i)) hpair
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi D).filtration b ω hF hf hfactor (fun i => by exact_mod_cast hlength i)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (_F : NativeAntisymmetricPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ k, mixedCorrelationDegree 1 k)
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have h2t : 2 ≤ t := by dsimp [t]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.antisymmetricPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.antisymmetricPairPolynomial) t := by
    have h := F.factorization
    rw [V.antisymmetricPairNiltest_symbol] at h
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration F.basis F.weight F.adapted h hrt (fun _ => by exact_mod_cast NeZero.pos N)
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.antisymmetricPairNiltest_complexity.1.mono D htest) (by simpa using h2t)
    (fun a b => (F.height a b).trans hrt) V.antisymmetricPairPolynomial
    (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
    (fun _ => (Real.exp_le_exp.mpr hcost).trans hN) hfactor
  exact ⟨R.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem pair_top_agreement (x : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
    (hx : x ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.antisymmetricPairFrequency_real] at h
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def pairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.antisymmetricPairModels k).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some k => ![(W.pairComponent a 0 1).conjugate, W.pairComponent b 1 0] k

theorem pairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.pairComparisonTests a b k).ComplexityLE (antisymmetricPairBudget p q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
      (V.antisymmetricPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact V.antisymmetricPairTests_complexity (some 0)
    · exact V.antisymmetricPairTests_complexity (some 1)

theorem pairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.antisymmetricPairModels k).RealGroup)
    (hz : z ∈ (V.antisymmetricPairModels k).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (V.antisymmetricPairModels k).Space) :
    (V.pairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.antisymmetricPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.pairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.pairComponent_vertical a 0 1) z hz x
    · exact W.pairComponent_vertical b 1 0 z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def pairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels (V.pairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    (V.pairComparisonTests_complexity a b)

theorem pairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.pairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels (V.pairComparisonTests a b) _ _ _

theorem pairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable x =
      star (W.vertical.observable a (productProjection V.antisymmetricPairModels (some 0) x)) *
        W.vertical.observable b (productProjection V.antisymmetricPairModels (some 1) x) := by
  change (∏ k, (V.pairComparisonTests a b k).observable
    (productProjection V.antisymmetricPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (star (W.vertical.observable a
    (productProjection V.antisymmetricPairModels (some 0) x)) *
      W.vertical.observable b (productProjection V.antisymmetricPairModels (some 1) x)) = _
  exact one_mul _

theorem pairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.antisymmetricPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.pairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.antisymmetricPairModels (V.pairComparisonTests a b)
    V.antisymmetricPairFrequencies _ _ _ (V.pairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable (z • x) =
      (V.pairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ k, mixedCorrelationDegree 1 k) :=
    (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.pairComparisonNiltest_vertical a b z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairFrozenVector (k : Fin 2)
    (a b : (pi V.antisymmetricPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.antisymmetricPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

theorem pairFrozenVector_unit (k : Fin 2)
    (a b : (pi V.antisymmetricPairModels).RealGroup) (x : Fin 2 → ℤ) :
    ∑ out, ‖R.pairFrozenVector k a b out x‖ ^ 2 = 1 :=
  W.vertical.unit _

def HasPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.antisymmetricPairModels).RealGroup,
      (∀ i, |((pi V.antisymmetricPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.antisymmetricPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
      NativeIntegerVectorEquivalence 1 b (R.pairFrozenVector 0 a r) (R.pairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_pair_frozen_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasPairFrozenEquivalence u ((p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion 1
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R _ _ _ _ hr hu m hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u
  let b := v + raisedNiltestBudget v + 4
  let t := productNiltestBudget b + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.antisymmetricPairModels) (R.mono hrt hN)
    (V.pairComparisonNiltest out₀ out₁) ht ((V.pairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.pair_comparison_invariant out₀ out₁) m hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((p + q + r + u + C) ^ C) (fun x =>
        star ((V.pairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x))))) :=
    ⟨F.conjugate.mono hcost⟩
  simpa only [V.pairComparisonNiltest_observable, star_mul, star_star,
    NativePolynomialOrbitFactors.pairFrozenVector, mul_comm] using hF

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  Nonempty (NativeAntisymmetricPairFactorization V ((p + C) ^ C)) := by
  obtain ⟨A, _, hcorr⟩ := exists_quadratic_pair_correlator
  obtain ⟨B, _, hdrop⟩ := exists_antisymmetric_pair_step_drop
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (2 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (2 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, hq, hqt, H, hH, hdense, M, i, hderiv, i', j', ⟨V⟩⟩ := hcorr hp f hf hG
  have hpair : (q + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + t + B ≤ 2 * t + B
    linarith
  obtain ⟨F⟩ := hdrop V ((Real.exp_le_exp.mpr hpair).trans hN)
  exact ⟨q, t, hq, hqt.trans htC, ht, htC, H, hH, hdense, M, i, hderiv, i', j', V,
    ⟨F.mono hpair⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
namespace OAI

universe u

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_vertical_selection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [LieRing L] [LieAlgebra ℚ L]
      {m d t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d) (ω : U → ℕ)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ M)
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit ω)
      (R : D.Niltest ω) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω (sample x) orbit)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationNilmanifold w d hw hwd).Niltest ω)
        (W : (D.raiseStep htd.le).Niltest ω),
        V.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        V.orbit = orbit ∧ V.normBound = 1 ∧
        W.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (raisedNiltestBudget p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((raisedNiltestBudget p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ m d t e w hw hd hwd _ _ _ _ _ _ _ _ _ D htd ω Ψ D₀ M hdegree hD
    orbit R p hp hgeometry hbound hR hRcap B hB sample multiplier hmultiplier hcorr
  let Q := weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD orbit
  have hQ : Q.ComplexityLE p :=
    weightedTranslationBufferedNiltest_complexity w d hw hwd ω hd Ψ D₀ M hdegree hD orbit
      hgeometry hbound
  have hraise := le_raisedNiltestBudget p
  have hraisedcorr : Real.exp (-(raisedNiltestBudget p)) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hraise)).trans
    simpa only [Q, weightedTranslationBufferedNiltest_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hcorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget p) (hp.trans hraise)
      (hQ.mono hraise) (R.raiseStep_complexity htd.le hp hR)
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_selected_frequency_one w d hw hd hwd Ψ D₀ η V.observable
      hvertV hVne hpresV
  exact ⟨η, V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne, hbias⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

abbrev PairAlgebra (L M : Type u) := ∀ i : Bool, BoolLieFamily L M i

def pairModels (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e) :
    ∀ i : Bool, RationalFilteredNilmanifold (BoolLieFamily L M i) s (Bool.rec e d i)
  | false => E
  | true => D

def pairFrequencies (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) :
    ∀ i : Bool, BoolLieFamily L M i →ₗ[ℚ] ℚ
  | false => θ
  | true => η

noncomputable def pairFrequency (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) :
    PairAlgebra L M →ₗ[ℚ] ℚ := piFrequency (pairFrequencies η θ)

@[simp] theorem pairFrequency_apply (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ)
    (x : PairAlgebra L M) : pairFrequency η θ x = η (x true) + θ (x false) := by
  rw [pairFrequency, piFrequency_apply, Fintype.sum_bool]
  rfl

variable (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    {σ ι : Type*} {w : σ → ℕ}

noncomputable def pairOrbit (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    (pi (pairModels D E)).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.piRealOrbit (fun i => (pairModels D E i).filtration)
    (fun i => by cases i; exact q; exact p)

noncomputable def pairOrbitSymbol (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pi (pairModels D E)).filtration.RealPolynomialSymbolGroup w :=
  (pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF w
    ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

noncomputable def pairTests (V : D.Niltest w) (W : E.Niltest w) :
    ∀ i : Bool, (pairModels D E i).Niltest w
  | false => W
  | true => V

theorem pairTests_complexity (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    ∀ i, (pairTests D E V W i).ComplexityLE p := by
  intro i
  cases i
  · exact hW
  · exact hV

section ProductTopology

variable [TopologicalSpace (ℝ ⊗[ℚ] PairAlgebra L M)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PairAlgebra L M)]
    [T2Space (ℝ ⊗[ℚ] PairAlgebra L M)]

noncomputable def pairNiltest (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pi (pairModels D E)).Niltest w :=
  piNiltest (pairModels D E) (pairTests D E V W) (by linarith)
    (by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp)
    (pairTests_complexity D E V W hV hW)

theorem pairNiltest_eval (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) (x : σ → ℤ) :
    (pairNiltest D E V W hp hV hW).eval x = V.eval x * W.eval x := by
  rw [pairNiltest, piNiltest_eval, Fintype.prod_bool]
  rfl

theorem pairNiltest_complexity (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pairNiltest D E V W hp hV hW).ComplexityLE (productNiltestBudget p) :=
  piNiltest_complexity (pairModels D E) (pairTests D E V W) (by linarith)
    (by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp)
    (pairTests_complexity D E V W hV hW)

@[simp] theorem pairNiltest_orbit (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pairNiltest D E V W hp hV hW).orbit = pairOrbit D E V.orbit W.orbit := rfl

@[simp] theorem pairNiltest_symbol (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pairNiltest D E V W hp hV hW).symbol b ω hF =
      pairOrbitSymbol D E V.orbit W.orbit b ω hF := rfl

end ProductTopology
end RationalFilteredNilmanifold

open RationalFilteredNilmanifold

theorem exists_native_pair_vertical_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p : ℝ} (_hp : 2 ≤ p) (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ),
          (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            V.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) →
          (∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
            W.observable (z • x) = CircleFourier.character
              ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, V.eval x * W.eval x‖ →
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun i => (lengths i : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_finite_product_vertical_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
  let models := pairModels D E
  let tests := pairTests D E V W
  let : FiniteDimensional ℚ (PairAlgebra L M) :=
    (productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra L M)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra L M) :=
    realification_moduleTopology_t2 (productFinBasis models)
  have hp0 : 0 ≤ p := by linarith
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  have htests : ∀ i, (tests i).ComplexityLE p := pairTests_complexity D E V W hV hW
  obtain ⟨b, ω, hF, hb, hconstruct⟩ := hstep models tests hp0 hcard htests
  refine ⟨b, ω, hF, hb, ?_⟩
  intro η θ hη hθ origin lengths hlengths hσ hlarge hbias
  have hvert : ∀ i z, z ∈ (models i).filtration.realification.subgroup s → ∀ x,
      (tests i).observable (z • x) = CircleFourier.character
        ((realifyFunctional (pairFrequencies η θ i) z.coord : ℝ) : CircleFourier.Circle) *
          (tests i).observable x := by
    intro i
    cases i
    · exact hθ
    · exact hη
  have hbias' : Real.exp (-p) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths, ∏ i, (tests i).eval x‖ := by
    have heval (x : σ → ℤ) : (∏ i, (tests i).eval x) = V.eval x * W.eval x := by
      rw [Fintype.prod_bool]
      rfl
    simp_rw [heval]
    exact hbias
  exact hconstruct (pairFrequencies η θ) hvert origin lengths hlengths hσ hlarge hbias'

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem pairFrequency_logHeight
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) {p : ℝ}
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθ : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (k : Fin (Fintype.card (Σ i : Bool, Fin (Bool.rec e d i)))) :
    rationalLogHeight (pairFrequency η θ ((pi (pairModels D E)).basis k)) ≤ p := by
  apply piFrequency_logHeight (pairModels D E) (pairFrequencies η θ)
  intro i
  cases i
  · exact hθ
  · exact hη

theorem exists_native_pair_positive_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p : ℝ} (_hp : 2 ≤ p) (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ),
          (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
          (∀ i, rationalLogHeight (θ (E.basis i)) ≤ p) →
          (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            V.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) →
          (∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
            W.observable (z • x) = CircleFourier.character
              ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, V.eval x * W.eval x‖ →
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun i => (lengths i : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF) ((p + C) ^ C) := by
  by_cases hs2 : 2 ≤ s
  · obtain ⟨C, hC, hstep⟩ := exists_native_pair_vertical_step_drop s hs2
    refine ⟨C, hC, ?_⟩
    intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
    obtain ⟨b, ω, hF, hb, hconstruct⟩ := hstep D E V W hp hV hW
    exact ⟨b, ω, hF, hb, fun η θ _ _ => hconstruct η θ⟩
  · have hs1 : s = 1 := by omega
    subst s
    let X : Polynomial ℕ := Polynomial.X
    let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + 2) ^ 4)
    refine ⟨C, hC, ?_⟩
    intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
    let models := pairModels D E
    let N := pi models
    let : FiniteDimensional ℚ (PairAlgebra L M) :=
      (productFinBasis models).finiteDimensional_of_finite
    let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra L M)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    let : T2Space (ℝ ⊗[ℚ] PairAlgebra L M) :=
      realification_moduleTopology_t2 (productFinBasis models)
    have hp0 : 0 ≤ p := by linarith
    have hpq : p ≤ productNiltestBudget p := by
      have hr := productObservableLipBudget_nonneg hp0
      unfold productNiltestBudget
      nlinarith [sq_nonneg (p + 2), sq_nonneg p]
    have hq : 0 ≤ productNiltestBudget p := hp0.trans hpq
    have hcost : (productNiltestBudget p + 2) ^ 4 ≤ (p + C) ^ C := by
      simpa [X, Q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
        using hbudget p hp0
    have hnonneg : 0 ≤ (p + C) ^ C := by positivity
    have hdim : finrank ℚ (PairAlgebra L M) =
        Fintype.card (Σ i : Bool, Fin (Bool.rec e d i)) := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis N.basis
    rw [hdim]
    let ω : Fin (Fintype.card (Σ i : Bool, Fin (Bool.rec e d i))) → ℕ := fun _ => 1
    have hF : ∀ k, N.filtration.layer k =
        Submodule.span ℚ (N.basis '' {i | k ≤ ω i}) :=
      N.filtration.stepOne_basis_layers N.basis
    refine ⟨N.basis, ω, hF, ?_, ?_⟩
    · intro i j
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simpa [rationalLogHeight] using hnonneg
    · intro η θ hηheight hθheight hη hθ origin lengths hlengths _hσ _hlarge hbias
      let T := pairNiltest D E V W hp hV hW
      have hT : T.ComplexityLE (productNiltestBudget p) :=
        pairNiltest_complexity D E V W hp hV hW
      have hfreq : ∀ i, rationalLogHeight (pairFrequency η θ (N.basis i)) ≤
          productNiltestBudget p :=
        fun i => (pairFrequency_logHeight D E η θ hηheight hθheight i).trans hpq
      have hvert : ∀ z, z ∈ N.filtration.realification.subgroup 1 → ∀ x,
          T.observable (z • x) = CircleFourier.character
            ((realifyFunctional (pairFrequency η θ) z.coord : ℝ) : CircleFourier.Circle) *
              T.observable x := by
        apply piNiltest_vertical (pairModels D E) (pairTests D E V W)
          (pairFrequencies η θ)
        intro i
        cases i
        · exact hθ
        · exact hη
      have hbias' : Real.exp (-productNiltestBudget p) ≤
          ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ := by
        simp_rw [show ∀ x, T.eval x = V.eval x * W.eval x from
          pairNiltest_eval D E V W hp hV hW]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
      have hf := N.stepOne_controlled_symbol_factorization ω hF T (pairFrequency η θ)
        hq hT hfreq hvert origin lengths hlengths hbias'
      have hf' := NilpotentLieFiltration.ControlledSymbolFactorization.mono
        N.filtration N.basis ω hF hf hcost (fun i => by exact_mod_cast hlengths i)
      exact hf'

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_correlation_step_drop (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ M)
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x orbit)) * R.eval x‖ →
      let N := pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hF : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d (by omega) 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
            orbit (D.raiseStepRealOrbit htd.le R.orbit) b ω hF) ((p + C) ^ C) := by
  obtain ⟨a, ha, hselect⟩ := exists_translation_major_vertical_selection
  obtain ⟨c, _hc, hstep⟩ := exists_native_pair_positive_step_drop d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorCorrelationBudget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd Ψ D₀ M hdegree hD
    orbit R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  dsimp only
  have hbox : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    exact ⟨le_rfl, by have hi := hlengths i; omega⟩
  obtain ⟨η, V, W, hVc, hVo, _hVn, hWc, hWo, _hWn, hheight, hη, hvertV, hvertW,
      _hVne, _hWne, hbias⟩ :=
    hselect w hw (by omega) hwd D htd (fun _ : U => 1) Ψ D₀ M hdegree hD
      orbit R p hp hgeometry hbound hR hRcap (translatedIntegerBox origin lengths) hbox
      (fun x => x) (fun _ => 1) (fun _ _ => by simp)
      (by simpa only [one_mul] using hcorr)
  let r := translationMajorPairBudget a p
  have hcontrols := translationMajorPairBudget_controls a hp ha
  have hpr : p ≤ r := hcontrols.1.trans hcontrols.2.1
  have hr : 2 ≤ r := hcontrols.2.2
  have hcost := hbudget p hp
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le) V W hr hVc hWc
  have hzeroheight : ∀ i, rationalLogHeight ((0 : L →ₗ[ℚ] ℚ)
      ((D.raiseStep htd.le).basis i)) ≤ r := by
    intro i
    simpa [rationalLogHeight] using (show 0 ≤ r by linarith)
  have hfactor := hconstruct η (0 : L →ₗ[ℚ] ℚ) hheight hzeroheight hvertV hvertW origin lengths hlengths
    (hU.trans hpr) (fun i => (Real.exp_le_exp.mpr hcost.2).trans (hlarge i))
    (by simpa only [one_mul, r, translationMajorPairBudget] using hbias)
  rw [hVo, hWo] at hfactor
  refine ⟨η, b, ω, hF, hη, fun i => (hheight i).trans hcost.1,
    fun i j => (hb i j).trans hcost.2, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hF hfactor hcost.2
    (fun i => by exact_mod_cast hlengths i)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_twisted_correlation_step_drop (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (B K : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ B)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ B K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x orbit)) * R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hF : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le) orbit (D.raiseStepRealOrbit htd.le R.orbit) b ω hF)
          ((p + C) ^ C) := by
  obtain ⟨a, ha, hselect⟩ := exists_translation_major_twisted_vertical_selection
  obtain ⟨c, _hc, hstep⟩ := exists_native_pair_positive_step_drop d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorCorrelationBudget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ D₀ B K hdegree hD
    T hT hLip orbit R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  dsimp only
  have hbox : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    exact ⟨le_rfl, by have hi := hlengths i; omega⟩
  obtain ⟨η, V, W, hVc, hVo, _hVn, hWc, hWo, _hWn, hheight, hη, hvertV, hvertW,
      _hVne, _hWne, hbias⟩ :=
    hselect w hw hd hwd M hM D htd (fun _ : U => 1) Ψ D₀ B K hdegree hD
      T hT hLip orbit R p hp hgeometry hbound hR hRcap
      (translatedIntegerBox origin lengths) hbox
      (fun x => x) (fun _ => 1) (fun _ _ => by simp)
      (by simpa only [one_mul] using hcorr)
  let r := translationMajorPairBudget a p
  have hcontrols := translationMajorPairBudget_controls a hp ha
  have hpr : p ≤ r := hcontrols.1.trans hcontrols.2.1
  have hr : 2 ≤ r := hcontrols.2.2
  have hcost := hbudget p hp
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (weightedTranslationResidueNilmanifold w d hw hwd M hM)
      (D.raiseStep htd.le) V W hr hVc hWc
  have hzero : ∀ i, rationalLogHeight
      ((0 : L →ₗ[ℚ] ℚ) ((D.raiseStep htd.le).basis i)) ≤ r := by
    intro i
    simpa [rationalLogHeight] using (show (0 : ℝ) ≤ r by linarith)
  have hfactor := hconstruct η (0 : L →ₗ[ℚ] ℚ) hheight hzero
    hvertV hvertW origin lengths hlengths (hU.trans hpr)
    (fun i => (Real.exp_le_exp.mpr hcost.2).trans (hlarge i))
    (by simpa only [one_mul, r, translationMajorPairBudget] using hbias)
  rw [hVo, hWo] at hfactor
  refine ⟨η, b, ω, hF, hη, fun i => (hheight i).trans hcost.1,
    fun i j => (hb i j).trans hcost.2, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hF hfactor hcost.2
    (fun i => by exact_mod_cast hlengths i)

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePairSymbolProjection
namespace OAI

universe sourceLevel

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

 theorem productProjection_repr (x : ∀ i, L i) (i : ι) (j : Fin (d i)) :
    (D i).basis.repr (x i) j =
      (pi D).basis.repr x (Fintype.equivFin (Σ i, Fin (d i)) ⟨i, j⟩) := by
  change _ = (productFinBasis D).repr x _
  rw [productFinBasis, Basis.repr_reindex_apply]
  simp only [Equiv.symm_apply_apply, Pi.basis_repr]

 theorem productProjection_coordinate_logHeight {p : ℝ} (x : ∀ i, L i)
    (hx : ∀ k, rationalLogHeight ((pi D).basis.repr x k) ≤ p) (i : ι) (j : Fin (d i)) :
    rationalLogHeight ((D i).basis.repr (x i) j) ≤ p := by
  rw [productProjection_repr D x i j]
  exact hx _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

 theorem pairFirstProjection_filtered (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e) (j : ℕ)
    (x : PairAlgebra L M) (hx : x ∈ (pi (pairModels D E)).filtration.layer j) :
    liePiEval (R := ℚ) true x ∈ D.filtration.layer j :=
  (NilpotentLieFiltration.mem_pi_layer (fun i => (pairModels D E i).filtration) j x).mp hx true

 theorem pairFrequency_zero_comp (η : L →ₗ[ℚ] ℚ) :
    pairFrequency η (0 : M →ₗ[ℚ] ℚ) =
      η.comp (liePiEval (R := ℚ) (M := BoolLieFamily L M) true).toLinearMap := by
  apply LinearMap.ext
  intro x
  change pairFrequency η (0 : M →ₗ[ℚ] ℚ) x = η (x true)
  rw [pairFrequency_apply]
  exact add_zero _

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold
variable {σ L : Type} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

theorem pairTranslationProjection_coordinate_logHeight {p : ℝ}
    (x : PairAlgebra (weightedSubalgebra w d) L)
    (hx : ∀ j, rationalLogHeight
      ((pi (pairModels (weightedTranslationNilmanifold w d hw hwd) D)).basis.repr x j) ≤ p)
    (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr (x true) i) ≤ p := by
  have h := productProjection_coordinate_logHeight
    (pairModels (weightedTranslationNilmanifold w d hw hwd) D) x hx true
    (weightedIndexOrder w d i)
  change rationalLogHeight ((weightedOrderedBasis w d hw).repr (x true)
    (weightedIndexOrder w d i)) ≤ p at h
  have he := weightedOrderedBasis_repr w d hw (x true) (weightedIndexOrder w d i)
  have he' : (weightedOrderedBasis w d hw).repr (x true) (weightedIndexOrder w d i) =
      (weightedBasis w d hw).repr (x true) i :=
    he.trans (congrArg ((weightedBasis w d hw).repr (x true)) ((weightedIndexOrder w d).symm_apply_apply i))
  exact he' ▸ h

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial
open scoped TensorProduct

variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ ι κ : Type*} (w : σ → ℕ)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels D E)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hG : ∀ j, D.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem pairOrbit_first_projection_log
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
      (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log = p.log := by
  let g : ∀ i : Bool, (pairModels D E i).filtration.realification.PolynomialOrbit w :=
    fun i => by cases i; exact q; exact p
  have h := NilpotentLieFiltration.piRealOrbit_projection_log
    (fun i => (pairModels D E i).filtration) g true
  change VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
      (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log = p.log at h
  exact h

theorem pairOrbitSymbol_first_projection
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    realificationLieHom
      ((pi (pairModels D E)).filtration.filteredPolynomialSymbolMap D.filtration
        (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E) w)
      (pairOrbitSymbol D E p q b ω hF).coord =
        D.filtration.realSymbolOfPolynomial c ν hG w p.log := by
  have h := (pi (pairModels D E)).filtration.realFilteredPolynomialSymbolMap_polynomial
    D.filtration (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E)
    b ω hF c ν hG w ⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩
  change realificationLieHom
      ((pi (pairModels D E)).filtration.filteredPolynomialSymbolMap D.filtration
        (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E) w)
      (pairOrbitSymbol D E p q b ω hF).coord =
    D.filtration.realSymbolOfPolynomial c ν hG w
      (VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
        (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log) at h
  refine h.trans (congrArg (D.filtration.realSymbolOfPolynomial c ν hG w) ?_)
  exact pairOrbit_first_projection_log D E w p q

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialData
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_translationMajorDetectedPotentialData (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (w : B → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      {e : ℕ} (D : RationalFilteredNilmanifold L d e),
      let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ∀ (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : σ => 1))
        (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (η : weightedSubalgebra w d →ₗ[ℚ] ℚ),
        η (centralRationalElement w d hd 1) = 1 →
      ∀ (T : σ → ℝ) (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
        (Fintype.card B : ℝ) ≤ p →
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) T
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            D orbit partner b ω hLayers) p →
      ∃ (l : ℕ) (E P R : N.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : ι → N.filtration.AssociatedGraded)
        (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial B ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
        E * P * R = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          D orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1) T (Real.exp p) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l R ∧
        (∀ t : σ → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : σ => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : σ => 1))
              P.coord)) ∈ realificationLieSubalgebra U) ∧
        U = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ p) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : σ => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_associatedGraded_controlled_potential d hd
  refine ⟨C, hC, ?_⟩
  intro σ B L ι _ _ _ _ w hw hwd _ M hM e D N orbit partner b ω hLayers η hη
    T p hp hι hB hb hfactor
  obtain ⟨l, E, P, R, W, v, hl, hlp, hprod, hE, hR, hv, hW, hheight, hkill, hP⟩ := hfactor
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  have hφ : ∀ j, ∀ x ∈ N.filtration.layer j, φ x ∈ (weightedFiltration w d hwd).layer j :=
    pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
  let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  have hkill' : ∀ x ∈ W,
      basisGradeProjection (N.filtration.associatedGradedBasis b ω hLayers) ω d x = x →
      N.filtration.gradedFrequency b ω hLayers (η.comp φ.toLinearMap) x = 0 := by
    simpa only [pairFrequency_zero_comp] using hkill
  obtain ⟨V, q, hV, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential N.filtration b ω hLayers w hw hwd φ hφ W hW v hv p hp hι hB
      hentries hheight η hη hkill'
  refine ⟨l, E, P, R, W, v, U, V, q, hl, hlp, hprod, hE, hR, ?_, rfl, hv, hW, hheight, hP, hV, hderiv,
    hq, hqp, hgrid, hmass, hcoeff⟩
  intro t
  have hm := N.filtration.projected_realSymbolRepresentative_mem_homogeneous_image
    (weightedFiltration w d hwd) b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ (fun _ : σ => 1) W P.coord hP t
  convert hm using 1
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDimensionBudget
namespace OAI

section

universe level

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ}

theorem finrank_eq_dimension (D : RationalFilteredNilmanifold L s d) :
    finrank ℚ L = d := by
  rw [finrank_eq_card_basis D.basis, Fintype.card_fin]

theorem geometry_finrank_le (D : RationalFilteredNilmanifold L s d) {p : ℝ}
    (hD : D.GeometryComplexityLE p) : (finrank ℚ L : ℝ) ≤ p := by
  rw [D.finrank_eq_dimension]
  exact hD.1

end RationalFilteredNilmanifold

namespace RationalFilteredNilmanifold

variable {L M : Type level} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ}

theorem geometry_pair_finrank_le (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p q : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE q) :
    (finrank ℚ (PairAlgebra L M) : ℝ) ≤ p + q := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ M := E.basis.finiteDimensional_of_finite
  let : ∀ i : Bool, Module.Finite ℚ (BoolLieFamily L M i) := by
    intro i
    cases i
    · exact (inferInstance : Module.Finite ℚ M)
    · exact (inferInstance : Module.Finite ℚ L)
  have hpair : finrank ℚ (PairAlgebra L M) = finrank ℚ L + finrank ℚ M := by
    change finrank ℚ (∀ i : Bool, BoolLieFamily L M i) = _
    rw [finrank_pi_fintype, Fintype.sum_bool]
    rfl
  rw [hpair, Nat.cast_add]
  exact add_le_add (D.geometry_finrank_le hD) (E.geometry_finrank_le hE)

end RationalFilteredNilmanifold

theorem two_mul_le_translation_major_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 2 ≤ a) :
    2 * p ≤ (p + (a : ℝ)) ^ a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hsq : 2 * p ≤ (p + (a : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (p + (a : ℝ) - 1)]
  exact hsq.trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + (a : ℝ)) ha)

namespace RationalFilteredNilmanifold

theorem geometry_pair_finrank_le_budget
    {L M : Type level} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    {a : ℕ} (ha : 2 ≤ a) :
    (finrank ℚ (PairAlgebra L M) : ℝ) ≤ (p + (a : ℝ)) ^ a := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hpair : (finrank ℚ (PairAlgebra L M) : ℝ) ≤ 2 * p := by
    simpa only [two_mul] using D.geometry_pair_finrank_le E hD hE
  exact hpair.trans (two_mul_le_translation_major_budget hp ha)

end RationalFilteredNilmanifold

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem card_le_weightedBasisIndex (w : σ → ℕ) (d : ℕ)
    [Fintype (WeightedBasisIndex w d)] :
    Fintype.card σ ≤ Fintype.card (WeightedBasisIndex w d) :=
  Fintype.card_le_of_injective (Sum.inl : σ → WeightedBasisIndex w d) Sum.inl_injective

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

theorem weightedTranslationResidueNilmanifold_base_card_le {p : ℝ}
    (hG : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p) :
    (Fintype.card σ : ℝ) ≤ p :=
  (Nat.cast_le.mpr (card_le_weightedBasisIndex w d)).trans hG.1

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AntisymmetricPairProjections
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def pairComponentPolynomial (out : Fin W.outputDim) (a b : Fin 2) :
    (W.model.filtration.realification.adaptedPolynomialFiltration (fun _ : Fin 2 => 1)).Group :=
  ⟨⟨(W.pairComponent out a b).orbit.log, (W.pairComponent out a b).orbit.property⟩⟩

end NativeMultidegreeNilcharacter

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem antisymmetricPairProjection_layers (k : Fin 2) (a : ℕ)
    (x : V.AntisymmetricPairAlgebra) (hx : x ∈ (pi V.antisymmetricPairModels).filtration.layer a) :
    V.antisymmetricPairProjection k x ∈ W.model.filtration.layer a :=
  (NilpotentLieFiltration.mem_pi_layer (fun l => (V.antisymmetricPairModels l).filtration) a x).mp hx (some k)

noncomputable def antisymmetricPairPolynomialMap (k : Fin 2) :
    ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group →*
        (W.model.filtration.realification.adaptedPolynomialFiltration (fun _ : Fin 2 => 1)).Group :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1)

theorem antisymmetricPairPolynomialMap_eq (k : Fin 2) (out : Fin W.outputDim) :
    V.antisymmetricPairPolynomialMap k V.antisymmetricPairPolynomial =
      W.pairComponentPolynomial out k k.rev := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom (liePiEval (some k))).toLinearMap.restrictScalars ℚ)
    (NilpotentLieFiltration.piRealOrbit (fun l => (V.antisymmetricPairModels l).filtration)
      (fun l => (V.antisymmetricPairTests l).orbit)).log = (W.pairComponent out k k.rev).orbit.log
  rw [NilpotentLieFiltration.piRealOrbit_projection_log]
  fin_cases k <;> rfl

theorem antisymmetricPairPolynomialMap_constant (k : Fin 2)
    (c : (pi V.antisymmetricPairModels).RealGroup) :
    V.antisymmetricPairPolynomialMap k
        ((pi V.antisymmetricPairModels).filtration.realification.adaptedConstantGroupHom
          (fun _ : Fin 2 => 1) c) =
      W.model.filtration.realification.adaptedConstantGroupHom (fun _ : Fin 2 => 1)
        (productProjectionHom V.antisymmetricPairModels (some k) c) :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap_constant W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1) c

theorem antisymmetricPairProjection_lattice (k : Fin 2)
    (c : (pi V.antisymmetricPairModels).RealGroup) (hc : c ∈ (pi V.antisymmetricPairModels).realLattice) :
    productProjectionHom V.antisymmetricPairModels (some k) c ∈ W.model.realLattice :=
  NilpotentLieBCHGroup.realificationMap_subgroup _ _ _
    (productProjection_lattice V.antisymmetricPairModels (some k)) hc

end NativeSampleCorrelation

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control 2 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.antisymmetricPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
      (fun k => (V.antisymmetricPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

namespace NativePolynomialOrbitFactors

variable (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
  V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
  (fun _ : Fin 2 => (N : ℝ)) r)

theorem pair_projected_product (k : Fin 2) (out : Fin W.outputDim) :
    V.antisymmetricPairPolynomialMap k R.slow * V.antisymmetricPairPolynomialMap k R.middle *
      V.antisymmetricPairPolynomialMap k R.rational *
        W.model.filtration.realification.adaptedConstantGroupHom (fun _ : Fin 2 => 1)
          (productProjectionHom V.antisymmetricPairModels (some k) R.latticeConstant) =
      W.pairComponentPolynomial out k k.rev := by
  have h := congrArg (V.antisymmetricPairPolynomialMap k) R.product
  simpa only [map_mul, V.antisymmetricPairPolynomialMap_constant,
    V.antisymmetricPairPolynomialMap_eq k out] using h

theorem pair_eval_component (k : Fin 2) (out : Fin W.outputDim) (n : Fin 2 → ℤ) :
    W.eval out (correlationInput (n k) (n k.rev)) =
      (W.pairComponent out k k.rev).observable (QuotientGroup.mk
        (W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.slow) *
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.middle) *
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.rational))) := by
  have h := Niltest.eval_of_lattice_factorization W.model (fun _ : Fin 2 => 1)
    (W.pairComponent out k k.rev) (V.antisymmetricPairPolynomialMap k R.slow)
    (V.antisymmetricPairPolynomialMap k R.middle) (V.antisymmetricPairPolynomialMap k R.rational)
    (productProjectionHom V.antisymmetricPairModels (some k) R.latticeConstant)
    (V.antisymmetricPairProjection_lattice k R.latticeConstant R.latticeConstant_mem)
    (R.pair_projected_product k out) n
  simpa only [W.pairComponent_eval] using h

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

theorem NativeSampleCorrelation.antisymmetricPairPolynomialMap_value
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
    (k : Fin 2)
    (g : ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group) (x : Fin 2 → ℝ) :
    W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) x
        (V.antisymmetricPairPolynomialMap k g) =
      productProjectionHom V.antisymmetricPairModels (some k)
        ((pi V.antisymmetricPairModels).filtration.adaptedPolynomialRealValueHom
          (fun _ : Fin 2 => 1) x g) :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap_value W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k)
    (fun _ : Fin 2 => 1) g x

namespace NativePolynomialOrbitFactors

variable (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
  V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
  (fun _ : Fin 2 => (N : ℝ)) r)

theorem pairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.eval out (correlationInput (x k) (x k.rev)) =
      R.pairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  rw [R.pair_eval_component k out x]
  simp only [pairFrozenVector, frozenMiddleValue, slowValue, rationalValue,
    productProjection_mk, map_mul, V.antisymmetricPairPolynomialMap_value]
  rfl

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem hasPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasPairFrozenEquivalence u b := by
  intro m hm hmb left right hleft hright
  exact (h m hm hmb left right hleft hright).mono hab

def HasPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasPairFrozenEquivalence u b

theorem hasPairFrozenReduction_mono {a b : ℝ}
    (h : R.HasPairFrozenReduction a) (hab : a ≤ b) : R.HasPairFrozenReduction b := by
  obtain ⟨u, hu, hua, houter, hequiv⟩ := h
  exact ⟨u, hu, hua.trans hab, houter, R.hasPairFrozenEquivalence_mono hequiv hab⟩

theorem pairFrozenEquivalence_at {b : ℝ} (h : R.HasPairFrozenReduction b)
    (x : Fin 2 → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence 1 b
      (R.pairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.pairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨m, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv m hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_pair_frozen_reduction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasPairFrozenReduction ((p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_antisymmetric_pair_outer_control
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_equivalence
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  exact ⟨u, hu, huC, houter R hr,
    R.hasPairFrozenEquivalence_mono (hfrozen R hr hu) hBC⟩

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

def HasPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin 2 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (correlationInput (x k) (x k.rev)) -
          R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

theorem hasPairLocalApproximation_mono {a b : ℝ}
    (h : R.HasPairLocalApproximation a) (hab : a ≤ b) : R.HasPairLocalApproximation b := by
  obtain ⟨P, hP, hPb, hlocal⟩ := h
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  exact (hlocal y hy k out x δ hδ hx hres hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) hδ)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin 2 → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.antisymmetricPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.antisymmetricPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.antisymmetricPairModels).basis.baseChange ℝ)
    ‖W.eval out (correlationInput (x k) (x k.rev)) -
        R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.antisymmetricPairModels
  let T := V.pairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 2 => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) := by
    have h := T.observable_budget (V.pairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.pairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.pairCoordinateNiltest_observable, pairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.pairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_local_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasPairLocalApproximation ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin 2) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.pairCoordinateNiltest_complexity 0 i).1.mono D htest
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.antisymmetricPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.pairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairAnchoredVector (y : Fin 2 → ℤ) (k : Fin 2) :
    Fin W.outputDim → (Fin 2 → ℤ) → ℂ :=
  R.pairFrozenVector k (R.slowValue y) (R.rationalValue y)

theorem pairAnchoredVector_norm (y : Fin 2 → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin 2 → ℤ) : ‖R.pairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

theorem select_pair_local_partition {b c : ℝ}
    (hlocal : R.HasPairLocalApproximation b) (hred : R.HasPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 2 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 2 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 1 c
            (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ (k : Fin 2) (out : Fin W.outputDim),
            (𝔼 x : Fin 2 → ZMod N,
              ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
                ∑ j, (A j x : ℂ) * R.pairAnchoredVector
                  (fun i => ((y j i).val : ℤ)) k out (fun i => ((x i).val : ℤ))‖) ≤
              Real.exp b * ρ + 4 * B.card / N := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 2 → ZMod N) (i : Fin 2) => ((x i).val : ℤ)
  have hv (x : Fin 2 → ZMod N) (i : Fin 2) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 2 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.pairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro k out
  let F := fun x : Fin 2 → ZMod N => W.eval out (correlationInput (v x k) (v x k.rev))
  let G := fun j (x : Fin 2 → ZMod N) => R.pairAnchoredVector (v (y j)) k out (v x)
  let E := coordinateExceptional (ι := Fin 2) B
  have hpoint (j : I) (x : Fin 2 → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - G j x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hmodel (v (y j)) (hv (y j)) k out (v x) ρ hρ (hv x) hres
      (by simpa only [v, Int.cast_natCast] using hnear)
  have hcap (x : Fin 2 → ZMod N) : ‖F x - ∑ j, (A j x : ℂ) * G j x‖ ≤ 2 := by
    apply norm_sub_positive_sum_le (fun j => A j x) (fun j => G j x) (F x) 2
      (fun j => hA j x) (hsum x)
    intro j _
    exact (norm_sub_le _ _).trans (by
      have hF : ‖F x‖ ≤ 1 := W.norm_eval out _
      have hG : ‖G j x‖ ≤ 1 := R.pairAnchoredVector_norm _ _ _ _
      linarith)
  have hgood (x : Fin 2 → ZMod N) (hx : x ∉ E) :
      ‖F x - ∑ j, (A j x : ℂ) * G j x‖ ≤ Real.exp b * ρ :=
    norm_sub_positive_sum_le (fun j => A j x) (fun j => G j x) (F x) (Real.exp b * ρ)
      (fun j => hA j x) (hsum x) (fun j => hpoint j x hx)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ‖F x - ∑ j, (A j x : ℂ) * G j x‖) (mul_nonneg (Real.exp_nonneg b) hρ)
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by simpa only [abs_of_nonneg (norm_nonneg _)] using hgood x hx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin 2) B
  have herr' : (𝔼 x : Fin 2 → ZMod N, ‖F x - ∑ j, (A j x : ℂ) * G j x‖) ≤
      Real.exp b * ρ + 2 * ((E.card : ℝ) / Fintype.card (Fin 2 → ZMod N)) := by
    simpa only [abs_of_nonneg (norm_nonneg _), mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + 2 * (2 * (B.card : ℝ) / N) := by gcongr
    _ = _ := by ring

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_pair_local_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ P : ℕ, ∃ hP : 0 < P,
        letI : NeZero P := ⟨hP.ne'⟩
        (P : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧
          (Fintype.card (Fin 2 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
          ∃ A : (Fin n × ZMod P) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            ∃ y : (Fin 2 → Fin n × ZMod P) → (Fin 2 → ZMod N),
              (∀ j, NativeIntegerVectorEquivalence 1 ((t + C) ^ C)
                (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
                (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
              ∀ (k : Fin 2) (out : Fin W.outputDim),
                (𝔼 x : Fin 2 → ZMod N,
                  ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
                    ∑ j, ((∏ i, A (j i) (x i) : ℝ) : ℂ) * R.pairAnchoredVector
                      (fun i => ((y j i).val : ℤ)) k out (fun i => ((x i).val : ℤ))‖) ≤
                  Real.exp (t + 40) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 40 + 2 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_pair_local_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 40 + 2 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have htwo : 2 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 2 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 2 => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, herr⟩ := hselect E w hρ.le hw hwSum hcells
  refine ⟨P, hP, hPt.trans (Real.exp_le_exp.mpr htC), n, hn, ?_, A,
    fun j => (hA j).mono le_rfl hcost, hsum, y,
    fun j => (hequiv j).mono (hct.trans htC), ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = Real.exp (2 * (t + B) ^ B) := (Real.exp_nat_mul _ 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr htwo
  · intro k out
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have h40 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
    apply (herr k out).trans
    calc
      _ = Real.exp b * ρ + 4 * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp t * ρ + 4 * (6 * ρ + 3 / N) := by gcongr
      _ ≤ Real.exp t * ρ + 4 * Real.exp t * (6 * ρ + 3 / N) := by
        gcongr
        nlinarith [Real.one_le_exp ht]
      _ = Real.exp t * (25 * ρ + 12 * (1 / N)) := by ring
      _ ≤ Real.exp t * (40 * (ρ + 1 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg t)
      _ = 40 * Real.exp t * (ρ + 1 / N) := by ring
      _ ≤ Real.exp 40 * Real.exp t * (ρ + 1 / N) := by gcongr
      _ = Real.exp (t + 40) * (ρ + 1 / N) := by rw [← Real.exp_add, add_comm 40 t]

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairCoordinate_common_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ l, mixedCorrelationDegree 1 l))
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency
          (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle) *
        (V.pairCoordinateNiltest k out).observable x := by
  have htop := (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le
    R.subalgebra _ hz
  have heq := R.pair_top_agreement z.coord hz
  rw [V.pairCoordinateNiltest_observable, productProjection_smul]
  have hv := W.pairComponent_vertical out k k.rev
    (productProjectionHom V.antisymmetricPairModels (some k) z)
    (productProjectionHom_mem_layer V.antisymmetricPairModels (some k) _ z htop)
    (productProjection V.antisymmetricPairModels (some k) x)
  change W.vertical.observable out _ = _ at hv
  refine hv.trans ?_
  change CircleFourier.character
      ((realifyFunctional W.vertical.frequency
        (realificationLieHom (V.antisymmetricPairProjection k) z.coord) : ℝ) : CircleFourier.Circle) *
      W.vertical.observable out _ = _
  have hphase : realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection k) z.coord) =
    realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) := by
    fin_cases k
    · rfl
    · exact heq.symm
  rw [hphase]
  exact congrArg (fun w : ℂ => CircleFourier.character
    ((realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle) * w)
      (V.pairCoordinateNiltest_observable k out x).symm

theorem pairCoordinate_comparison_invariant (k l : Fin 2) (i j : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ l, mixedCorrelationDegree 1 l))
    (x y : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k i).observable (z • x) *
      star ((V.pairCoordinateNiltest l j).observable (z • y)) =
    (V.pairCoordinateNiltest k i).observable x * star ((V.pairCoordinateNiltest l j).observable y) := by
  let c := CircleFourier.character
    ((realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    dsimp only [c]
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  rw [R.pairCoordinate_common_vertical k i z hz x,
    R.pairCoordinate_common_vertical l j z hz y, star_mul]
  change (c * _) * (_ * star c) = _
  calc
    _ = (c * star c) * ((V.pairCoordinateNiltest k i).observable x *
      star ((V.pairCoordinateNiltest l j).observable y)) := by ring
    _ = _ := by rw [hc, one_mul]

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_anchor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → R.HasOuterValueControl u →
      ∀ y z : Fin 2 → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
        (∀ k, |(z k : ℝ)| ≤ (N : ℝ)) → ∀ k l : Fin 2,
        NativeIntegerVectorEquivalence 1 ((p + q + r + u + C) ^ C)
          (R.pairAnchoredVector y k) (R.pairAnchoredVector z l) := by
  obtain ⟨A, _, hcomparison⟩ := exists_native_frozen_comparison 1
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R hr hu houter y z hy hz k l
  let := moduleTopology ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u
  let b := v + raisedNiltestBudget v + 4
  let t := productNiltestBudget b + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + A) ^ A ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + q + r + u + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + A) ^ A ≤ (p + q + r + u + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hcap (k : Fin 2) (out : Fin W.outputDim) (x : (pi V.antisymmetricPairModels).Space) :
      ‖(V.pairCoordinateNiltest k out).observable x‖ ≤ 1 := by
    rw [V.pairCoordinateNiltest_observable]
    exact W.vertical.norm out _
  obtain ⟨E⟩ := hcomparison (pi V.antisymmetricPairModels) (R.mono hrt hN)
    ![V.pairCoordinateNiltest k out₀, V.pairCoordinateNiltest l out₁] ht
    (by intro a; fin_cases a
        · exact (V.pairCoordinateNiltest_complexity k out₀).mono htest
        · exact (V.pairCoordinateNiltest_complexity l out₁).mono htest)
    (by intro a x; fin_cases a
        · exact hcap k out₀ x
        · exact hcap l out₁ x)
    (fun a ha x y => R.pairCoordinate_comparison_invariant k l out₀ out₁ a ha x y)
    m hm (hmb.trans (Real.exp_le_exp.mpr hut))
    ![R.slowValue y, R.slowValue z] ![R.rationalValue y, R.rationalValue z]
    (by intro a e; fin_cases a
        · exact (hslow y hy e).trans (Real.exp_le_exp.mpr hut)
        · exact (hslow z hz e).trans (Real.exp_le_exp.mpr hut))
    (by intro a; fin_cases a
        · exact hrat y
        · exact hrat z)
  simpa only [V.pairCoordinateNiltest_observable, NativePolynomialOrbitFactors.pairAnchoredVector,
    NativePolynomialOrbitFactors.pairFrozenVector] using
    (show Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + r + u + C) ^ C)
      (fun x => (V.pairCoordinateNiltest k out₀).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x)) *
        star ((V.pairCoordinateNiltest l out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue z) (R.rationalValue z) x))))) from
      ⟨E.mono hcost⟩)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors.FrozenMiddleRealization

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r}
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.antisymmetricPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

end NativePolynomialOrbitFactors.FrozenMiddleRealization

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

variable {R}
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.antisymmetricPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

end NativePolynomialOrbitFactors
end Erdos3

end

end OAI

end


