-- Prove2me | Definitions.Def_OAIErdos3B107
-- name    : OAIErdos3B107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:03:20.696989+00:00
-- url     : https://prove2.me/theorems/b14455cf-5d7b-47d5-a865-581237e80e4d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 108 of 132
-- statement:
--   Definitions bundle 108 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B106`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 108 available.
--
--   Modules: `OAI.Erdos3.CyclicNiltestUpperComparison.normalize`, `OAI.Erdos3.CyclicShiftComparison`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.comparison_deep_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.comparison_lie_deep_mem`, `OAI.Erdos3.NilpotentLieFiltration.exists_realSquarePolynomial_lift`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_normalizedRelative_preimage`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_normalized_square_factors`, `OAI.Erdos3.NilpotentLieFiltration.exists_stepOne_linear_splitting`, `OAI.Erdos3.NilpotentLieFiltration.mem_real_stepOneFrequencyKernel`, `OAI.Erdos3.NilpotentLieFiltration.mem_stepOneGradedKernel`, `OAI.Erdos3.NilpotentLieFiltration.nativeNormalizedSquareObservable_product`, `OAI.Erdos3.NilpotentLieFiltration.nativeNormalizedSquareOrbit_fst`, `OAI.Erdos3.NilpotentLieFiltration.nativeSquareOrbit_fst`, `OAI.Erdos3.NilpotentLieFiltration.nativeSquareOrbit_snd`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupHom_injective`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_normalized`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedRelative_mem_iff_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedRelative_polynomial_surjective`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeCoefficient_of_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realRelativeSquarePolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realSquareDiagonalPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.realSquareDifference_mem_two`, `OAI.Erdos3.NilpotentLieFiltration.realSquareFstPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.realSquareFstPolynomialHom_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.realSquareFstPolynomialHom_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realSquareFstPolynomialHom_relative`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable_lipschitz`, `OAI.Erdos3.NilpotentLieFiltration.realSquarePolynomial_ext`, `OAI.Erdos3.NilpotentLieFiltration.realSquarePolynomial_factorization`, `OAI.Erdos3.NilpotentLieFiltration.realSquarePolynomial_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.realSquareSndPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.realSquareSndPolynomialHom_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.realSquareSndPolynomialHom_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realSquareSndPolynomialHom_relative`, `OAI.Erdos3.NilpotentLieFiltration.real_normalized_square_coefficient_identity`, `OAI.Erdos3.NilpotentLieFiltration.real_refiltered_lieTreeEval_mem`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquarePolynomial_adapted`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquarePolynomial_fst`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquarePolynomial_snd`, `OAI.Erdos3.NilpotentLieFiltration.stepOneFrequencyKernel`, `OAI.Erdos3.NilpotentLieFiltration.stepOneGradedEquiv`, `OAI.Erdos3.NilpotentLieFiltration.stepOneGradedEquiv_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.stepOneGradedFrequency`, `OAI.Erdos3.NilpotentLieFiltration.stepOneGradedFrequency_equiv`, `OAI.Erdos3.NilpotentLieFiltration.stepOneGradedKernel`, `OAI.Erdos3.NilpotentLieFiltration.stepOneGradedKernel_span`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_basis_layers`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_basis_weight`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_gradedPieceProjection`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_gradedPieceProjection_mem_kernel`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_graded_submodule`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_symbol_linearPart`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_symbol_values_in_gradedKernel`, `OAI.Erdos3.PolynomialTranslationLie.base_gradeProjection`, `OAI.Erdos3.PolynomialTranslationLie.basisGradedSubmodule_ambient_base_image`, `OAI.Erdos3.PolynomialTranslationLie.exists_controlled_graded_base_coordinates`, `OAI.Erdos3.PolynomialTranslationLie.submoduleBasisCoordinates`, `OAI.Erdos3.PolynomialTranslationLie.submoduleBasisCoordinates_injective`, `OAI.Erdos3.PolynomialTranslationLie.submoduleBasisCoordinates_range`, `OAI.Erdos3.PolynomialTranslationLie.submoduleBasisCoordinates_single`, `OAI.Erdos3.PolynomialTranslationLie.weightedBaseLinear`, `OAI.Erdos3.PolynomialTranslationLie.weightedBaseLinear_apply`, `OAI.Erdos3.PositiveCyclicModel.coordinateTest`, `OAI.Erdos3.PositiveCyclicModel.coordinateTest_complexity`, `OAI.Erdos3.PositiveCyclicModel.coordinateTest_eval`, `OAI.Erdos3.PositiveCyclicModel.coordinateTest_evalCyclic`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.ControlledRankBracketFactorization`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.ControlledRankBracketFactorization.exists_in`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.ControlledRankBracketFactorization.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.controlledRankBracketFactorization_of_frequency_restriction`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.real_refiltered_rank_bracket_frequency`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.castDimension`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.castDimension_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.castDimension_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.castDimension_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.castDimension_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.PrescribedSquareImagePartitionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.SquareImageRecoverySpec`, `OAI.Erdos3.RationalFilteredNilmanifold.castDimension`, `OAI.Erdos3.RationalFilteredNilmanifold.castDimension_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_native_product_approximation`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_factorwise_covers`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_product_partition_approximation`, `OAI.Erdos3.RationalFilteredNilmanifold.integerOrbitPoint_translate`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeRefilteredMap`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeRefilteredTarget`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjectionHom_pi_symm`, `OAI.Erdos3.RationalFilteredNilmanifold.refilteredComponentMap`, `OAI.Erdos3.ResidueBoxSlice.identity_point`, `OAI.Erdos3.ResidueBoxSlice.integerPolynomial`, `OAI.Erdos3.ResidueBoxSlice.integerPolynomial_eval`, `OAI.Erdos3.ResidueBoxSlice.reindexInteger`, `OAI.Erdos3.ResidueBoxSlice.reindexInteger_eval`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedGridPointCap`, `OAI.Erdos3.VectorPolynomial.forecastCoefficientOutputHom`, `OAI.Erdos3.VectorPolynomial.forecastCongruenceOutput`, `OAI.Erdos3.VectorPolynomial.forecastSpatialOutputHom`, `OAI.Erdos3.bchSubgroup_inner_grid_of_reindex`, `OAI.Erdos3.exists_bounded_realified_square_polynomial`, `OAI.Erdos3.exists_controlled_basisGraded_coordinate_basis`, `OAI.Erdos3.exists_positive_coordinate_product`, `OAI.Erdos3.intervalTensorApprox`, `OAI.Erdos3.intervalTensorWeight`, `OAI.Erdos3.productPartitionWeight`, `OAI.Erdos3.productPartitionWeight_diameter`, `OAI.Erdos3.productPartitionWeight_nonneg`, `OAI.Erdos3.productPartitionWeight_pos_coordinate`, `OAI.Erdos3.realifyFunctional_eq_on_submodule`, `OAI.Erdos3.realifyFunctional_sub_apply`, `OAI.Erdos3.sum_productPartitionWeight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B106

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ComparisonLayerBracket
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonGraphLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonGraphLayer π i) (hy : y ∈ F.comparisonGraphLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonGraphLayer π (i + j) := by
  refine F.comparisonGraphLayer_induction π i
    (P := fun z => ⁅z, y⁆ ∈ F.comparisonGraphLayer π (i + j)) hx ?_ ?_ ?_
  · intro a ha hia u
    refine F.comparisonGraphLayer_induction π j
      (P := fun z => ⁅F.comparisonGraph π a ha u, z⁆ ∈ F.comparisonGraphLayer π (i + j)) hy ?_ ?_ ?_
    · intro b hb hjb v
      have hab : a + b ≠ 0 := by
        intro h
        apply ha
        funext k
        change a k = 0
        have hk : a k + b k = 0 := congrFun h k
        omega
      rw [F.comparisonGraph_lie π a b ha hb hab u v]
      apply F.comparisonGraph_mem_graphLayer π (i + j) (a + b) hab
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using Nat.add_le_add hia hjb
    · rw [lie_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [lie_add]
      exact Submodule.add_mem _ hv hw
  · rw [zero_lie]
    exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparison_deep_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonProductLayer π (i + 1)) (hy : y ∈ F.comparisonLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  apply (le_sup_left : F.comparisonProductLayer π (i + j + 1) ≤ F.comparisonLayer π (i + j))
  simpa only [Nat.add_right_comm i 1 j] using
    F.comparisonProductLayer_lie_mem π hx (F.comparisonLayer_le_product π j hy)

theorem comparison_lie_deep_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonLayer π i) (hy : y ∈ F.comparisonProductLayer π (j + 1)) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  apply (le_sup_left : F.comparisonProductLayer π (i + j + 1) ≤ F.comparisonLayer π (i + j))
  simpa only [Nat.add_assoc] using
    F.comparisonProductLayer_lie_mem π (F.comparisonLayer_le_product π i hx) hy

theorem comparisonLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonLayer π i) (hy : y ∈ F.comparisonLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_lie]
  apply Submodule.add_mem _ (F.comparison_deep_lie_mem π hu hy)
  obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [lie_add]
  apply Submodule.add_mem _
    (F.comparison_lie_deep_mem π
      ((le_sup_right : F.comparisonGraphLayer π i ≤ F.comparisonLayer π i) hv) hz)
  exact (le_sup_right : F.comparisonGraphLayer π (i + j) ≤ F.comparisonLayer π (i + j))
    (F.comparisonGraphLayer_lie_mem π hv hw)

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PositiveCyclicCoordinateProduct
namespace OAI

section

universe u

namespace Erdos3.PositiveCyclicModel

open scoped TensorProduct

attribute [local instance] PositiveCyclicModel.lie PositiveCyclicModel.algebra PositiveCyclicModel.topology PositiveCyclicModel.topologicalAdd PositiveCyclicModel.continuousSMul PositiveCyclicModel.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
  (R : PositiveCyclicModel.{u} s N p f) {σ : Type*} [Fintype σ]

noncomputable def coordinateTest (i : σ) : R.model.Niltest (fun _ : σ => 1) :=
  R.test.linearPullbackHom (fun _ : Unit =>
    { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl })

theorem coordinateTest_eval (i : σ) (x : σ → ℤ) :
    (R.coordinateTest i).eval x = R.test.eval (fun _ => x i) := by
  exact R.test.eval_linearPullbackHom _ x

theorem coordinateTest_complexity (i : σ) :
    (R.coordinateTest i).ComplexityLE p := R.complexity

theorem coordinateTest_evalCyclic (i : σ) (x : σ → ZMod N) :
    (R.coordinateTest i).evalCyclic N x = (f (x i) : ℂ) := by
  change (R.coordinateTest i).eval (fun j => ((x j).val : ℤ)) = _
  rw [R.coordinateTest_eval]
  apply Complex.ext
  · exact (R.eval (x i)).symm
  · simpa only [Complex.ofReal_im] using
      (R.test.unit_interval_eval R.positive (fun _ => ((x i).val : ℤ))).1

end Erdos3.PositiveCyclicModel

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] PositiveCyclicModel.lie PositiveCyclicModel.algebra PositiveCyclicModel.topology PositiveCyclicModel.topologicalAdd PositiveCyclicModel.continuousSMul PositiveCyclicModel.hausdorff

theorem exists_positive_coordinate_product {σ : Type} [Fintype σ]
    {s N : ℕ} [NeZero N] {p : ℝ} {f : σ → ZMod N → ℝ}
    (hp : 0 ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hf : ∀ i, PositiveCyclicNiltest.{0} s N p (f i)) :
    ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
        (productNiltestBudget (raisedNiltestBudget p)) g) ∧
      ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) = ∏ i, (f i (x i) : ℂ) := by
  classical
  let R := fun i => Classical.choice ((hf i).model_nonempty hp)
  let D := fun i => (R i).model
  let T := fun i => (R i).coordinateTest i
  let : FiniteDimensional ℚ (∀ i, (R i).L) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, (R i).L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, (R i).L)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, (R i).L)) := realification_moduleTopology_t2 (productFinBasis D)
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hσ' : (Fintype.card σ : ℝ) ≤ raisedNiltestBudget p := hσ.trans (le_raisedNiltestBudget p)
  have hT : ∀ i, (T i).ComplexityLE (raisedNiltestBudget p) :=
    fun i => (R i).coordinateTest_complexity i
  let S := piNiltest D T hp' hσ' hT
  refine ⟨S.eval, ⟨NativeIntegerExpansion.ofTest S
    (piNiltest_complexity D T hp' hσ' hT) (fun _ => rfl)⟩, ?_⟩
  intro x
  change (piNiltest D T hp' hσ' hT).eval _ = _
  rw [piNiltest_eval]
  apply Finset.prod_congr rfl
  intro i _
  exact (R i).coordinateTest_evalCyclic i x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

noncomputable def productPartitionWeight (j : ∀ a, κ a) (x : ∀ a, X a) : ℝ :=
  ∏ a, ψ a (j a) (x a)

theorem productPartitionWeight_nonneg (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) : 0 ≤ productPartitionWeight ψ j x :=
  Finset.prod_nonneg (fun a _ => hψ a (j a) (x a))

theorem productPartitionWeight_pos_coordinate (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) (hx : 0 < productPartitionWeight ψ j x) (a : α) :
    0 < ψ a (j a) (x a) := by
  classical
  apply lt_of_le_of_ne (hψ a (j a) (x a))
  intro hz
  have hw : productPartitionWeight ψ j x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ a) hz.symm
  linarith

variable [DecidableEq α] [∀ a, Fintype (κ a)]

theorem sum_productPartitionWeight (hsum : ∀ a x, ∑ j, ψ a j x = 1) (x : ∀ a, X a) :
    ∑ j, productPartitionWeight ψ j x = 1 := by
  unfold productPartitionWeight
  rw [← Fintype.prod_sum (fun a j => ψ a j (x a))]
  simp only [hsum, Finset.prod_const_one]

variable [∀ a, PseudoMetricSpace (X a)]

omit [DecidableEq α] [∀ a, Fintype (κ a)] in
theorem productPartitionWeight_diameter {rho : ℝ} (hrho : 0 ≤ rho)
    (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (hdiam : ∀ a j x y, 0 < ψ a j x → 0 < ψ a j y → dist x y ≤ rho)
    (j : ∀ a, κ a) (x y : ∀ a, X a)
    (hx : 0 < productPartitionWeight ψ j x) (hy : 0 < productPartitionWeight ψ j y) :
    dist x y ≤ rho := by
  apply (dist_pi_le_iff hrho).mpr
  intro a
  exact hdiam a (j a) (x a) (y a)
    (productPartitionWeight_pos_coordinate ψ hψ j x hx a)
    (productPartitionWeight_pos_coordinate ψ hψ j y hy a)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def intervalTensorWeight {S : Type*} [Fintype S] (B r : ℝ)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : ℝ :=
  ∏ i, intervalSiteWeight B r (k i) (x i)

noncomputable def intervalTensorApprox {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (F : (S → ℝ) → ℂ) (x : S → ℝ) : ℂ :=
  ∑ k : S → Fin (intervalSiteCount B r),
    (intervalTensorWeight B r k x : ℂ) * F (fun i => intervalSiteCenter B r (k i))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_native_product_partition_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0), LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤
                  (ell : ℝ) * (productMetricBound d : ℝ) * rho := by
  obtain ⟨C, hC, hpart⟩ := exists_native_factor_partitions s a
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, hdiam⟩ :=
    hpart D hp hα hD hrho hscale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hv hbound
  let F := v ∘ (productSpaceEquiv D).symm
  have hF : LipschitzWith (ell * productMetricBound d) F :=
    hv.comp (productSpaceEquiv_symm_lipschitz D)
  obtain ⟨c, hc, herr⟩ := exists_bounded_complex_partition_approximation
    (productPartitionWeight ψ) (productPartitionWeight_nonneg ψ (fun i j x => (hunit i j x).1))
    (sum_productPartitionWeight ψ hsum)
    (productPartitionWeight_diameter ψ hrho.le (fun i j x => (hunit i j x).1) hdiam)
    F 2 (fun x => hbound _) hF
  refine ⟨c, hc, fun x => ?_⟩
  have h := herr (productSpaceEquiv D x)
  simp only [F, Function.comp_apply, Equiv.symm_apply_apply, productPartitionWeight,
    productSpaceEquiv_apply, NNReal.coe_mul] at h
  push_cast at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_controlled_native_product_approximation (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p epsilon : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0),
              (ell : ℝ) ≤ Real.exp ((p + 2) ^ b) → LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨c, _, hpart⟩ := exists_native_product_partition_approximation s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 2) ^ a + (X + 2) ^ b + (X + 4) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p epsilon hp hα hD hepsilon hscale
  let q := p + (p + 2) ^ a + (p + 2) ^ b + (p + 4) ^ 4
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [pow_nonneg (by linarith : 0 ≤ p + 2) a,
      pow_nonneg (by linarith : 0 ≤ p + 2) b, sq_nonneg ((p + 4) ^ 2)]
  have hq : 0 ≤ q := hp.trans hpq
  let A := (p + 2) ^ b + (p + 4) ^ 4
  let rho := epsilon / Real.exp A
  have hrho : 0 < rho := div_pos hepsilon (Real.exp_pos _)
  have hrhoscale : 1 / rho ≤ Real.exp ((q + 2) ^ 1) := by
    calc
      1 / rho = Real.exp A * (1 / epsilon) := by dsimp [rho]; field_simp
      _ ≤ Real.exp A * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
      _ = Real.exp (A + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A, q]; simp only [pow_one]; linarith)
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happ⟩ :=
    hpart D hq (hα.trans hpq) (fun i => (hD i).mono (D i) hpq) hrho hrhoscale
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hell hv hb
  obtain ⟨coeff, hcoeff, herr⟩ := happ v ell hv hb
  refine ⟨coeff, hcoeff, fun x => (herr x).trans ?_⟩
  calc
    (ell : ℝ) * (productMetricBound d : ℝ) * rho ≤
        Real.exp ((p + 2) ^ b) * Real.exp ((p + 4) ^ 4) * rho :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hell (productMetricBound_le_exp d hp hα (fun i => (hD i).1))
          (productMetricBound d).coe_nonneg (Real.exp_nonneg _)) hrho.le
    _ = epsilon := by rw [← Real.exp_add]; dsimp [rho, A]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realifiedSquarePolynomial_fst
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra) :
    VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) =
        VectorPolynomial.map F.realification.squareFst.toLinearMap p := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  have h := F.realifiedSquareEquiv_fst (F.realifiedSquareEquiv.symm (coefficients p α))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem realifiedSquarePolynomial_snd
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra) :
    VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) =
        VectorPolynomial.map F.realification.squareSnd.toLinearMap p := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  have h := F.realifiedSquareEquiv_snd (F.realifiedSquareEquiv.symm (coefficients p α))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem realifiedSquarePolynomial_adapted (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra)
    (hp : F.realification.squareFiltration.Adapted w p) :
    F.squareFiltration.realification.Adapted w
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) :=
  F.realification.squareFiltration.adapted_map F.squareFiltration.realification
    F.realifiedSquareEquiv.symm.toLinearMap
    (fun j x hx => (F.realifiedSquareEquiv_symm_mem_layer j x).mpr hx) w hp

end NilpotentLieFiltration

theorem exists_bounded_realified_square_polynomial (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℚ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ r : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra),
          D.filtration.squareFiltration.realification.Adapted w r ∧
          VectorPolynomial.map
            ((realificationLieHom D.filtration.squareFst).toLinearMap.restrictScalars ℚ) r =
              normalizedShiftLog s h (-ε.coord) (-γ.coord) f.log ∧
          VectorPolynomial.map
            ((realificationLieHom D.filtration.squareSnd).toLinearMap.restrictScalars ℚ) r = f.log := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, r, hr, hf, hs⟩ := hnorm D p hp hD w hw h f
  refine ⟨ε, γ, hγ, hε, VectorPolynomial.map D.filtration.realifiedSquareEquiv.symm.toLinearMap r,
    D.filtration.realifiedSquarePolynomial_adapted w r hr, ?_, ?_⟩
  · rw [D.filtration.realifiedSquarePolynomial_fst]
    exact hf
  · rw [D.filtration.realifiedSquarePolynomial_snd]
    exact hs

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realSquareFstPolynomialHom :
    F.squareFiltration.RealAdaptedPolynomialGroup w →* F.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot) (F.squareFstPolynomialMap w)

noncomputable def realSquareSndPolynomialHom :
    F.squareFiltration.RealAdaptedPolynomialGroup w →* F.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot) (F.squareSndPolynomialMap w)

theorem realSquareFstPolynomialHom_polynomial (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ)
        (F.squareFiltration.realAdaptedPolynomialMap w r.coord) :=
  F.squareFiltration.realFilteredPolynomialMap_polynomial F F.squareFst (fun _ _ hx => hx.1) w r.coord

theorem realSquareSndPolynomialHom_polynomial (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord =
      VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ)
        (F.squareFiltration.realAdaptedPolynomialMap w r.coord) :=
  F.squareFiltration.realFilteredPolynomialMap_polynomial F F.squareSnd (fun _ _ hx => hx.2.1) w r.coord

theorem realSquarePolynomial_ext {r q : F.squareFiltration.RealAdaptedPolynomialGroup w}
    (hf : F.realSquareFstPolynomialHom w r = F.realSquareFstPolynomialHom w q)
    (hs : F.realSquareSndPolynomialHom w r = F.realSquareSndPolynomialHom w q) : r = q := by
  let P := (F.squareFstPolynomialMap w).toLinearMap.prod (F.squareSndPolynomialMap w).toLinearMap
  have hP : Function.Injective P := by
    intro x y hxy
    exact F.square_polynomial_ext w (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have hPR := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) P hP
  apply NilpotentLieBCHGroup.ext
  apply hPR
  apply (TensorProduct.prodRight ℚ ℝ ℝ (F.adaptedLieSubalgebra w) (F.adaptedLieSubalgebra w)).injective
  change TensorProduct.prodRight ℚ ℝ ℝ _ _ (P.baseChange ℝ r.coord) =
    TensorProduct.prodRight ℚ ℝ ℝ _ _ (P.baseChange ℝ q.coord)
  rw [realification_prod, realification_prod]
  exact Prod.ext (congrArg NilpotentLieBCHGroup.coord hf) (congrArg NilpotentLieBCHGroup.coord hs)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem exists_realSquarePolynomial_lift (p : F.squareFiltration.realification.adaptedLieSubalgebra w) :
    ∃ r : F.squareFiltration.RealAdaptedPolynomialGroup w,
      F.squareFiltration.realAdaptedPolynomialMap w r.coord = p.val ∧
      F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
        VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ) p.val ∧
      F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord =
        VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ) p.val := by
  obtain ⟨x, hx⟩ := F.squareFiltration.realAdaptedPolynomialTensor_surjective w
    (F.adaptedSquareBasis b ω (hF 2)) (squareBasisWeight ω) (F.adaptedSquareBasis_layers b ω hF) p
  have hp := congrArg (fun z : F.squareFiltration.realification.adaptedLieSubalgebra w => z.val) hx
  change F.squareFiltration.realAdaptedPolynomialMap w x = p.val at hp
  refine ⟨⟨x⟩, hp, ?_, ?_⟩
  · rw [F.realSquareFstPolynomialHom_polynomial, hp]
  · rw [F.realSquareSndPolynomialHom_polynomial, hp]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedPolynomialMap_coefficient
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedPolynomialMap w x) α = (F.adaptedCoefficientMap w α).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r p => rw [F.realAdaptedPolynomialMap_coefficient_tmul]; rfl

include b ω hF in
theorem realNormalizedRelative_mem_iff_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    x ∈ (F.normalizedRelativeSubmodule w).baseChange ℝ ↔
      F.realAdaptedPolynomialTensor w x ∈ F.realification.normalizedRelativeSubmodule w := by
  change x ∈ ((F.shiftedAdaptedIdeal w).toSubmodule ⊓
    (F.layer 2).comap (F.adaptedCoefficientMap w 0)).baseChange ℝ ↔ _
  rw [realification_inf, realification_comap]
  change (x ∈ F.realShiftedCoefficientSubmodule w 1 ∧
    (F.adaptedCoefficientMap w 0).baseChange ℝ x ∈ F.realification.layer 2) ↔
    (F.realAdaptedPolynomialTensor w x ∈ F.realification.shiftedPolynomialIdeal w 1 ∧
      coefficients (F.realAdaptedPolynomialMap w x) 0 ∈ F.realification.layer 2)
  rw [F.realShiftedCoefficient_mem_iff_tensor b ω hF,
    F.realAdaptedPolynomialMap_coefficient]

include b ω hF in
theorem realNormalizedRelative_polynomial_surjective
    (p : F.realification.normalizedRelativeSubmodule w) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w,
      F.realAdaptedPolynomialTensor w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x) = p.val := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p.val
  have hmem : x ∈ (F.normalizedRelativeSubmodule w).baseChange ℝ := by
    apply (F.realNormalizedRelative_mem_iff_tensor b ω hF w x).mpr
    rw [hx]
    exact p.property
  let y := (realificationSubmoduleEquiv (F.normalizedRelativeSubmodule w)).symm ⟨x, hmem⟩
  have hy : (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ y = x :=
    congrArg Subtype.val ((realificationSubmoduleEquiv (F.normalizedRelativeSubmodule w)).apply_symm_apply ⟨x, hmem⟩)
  exact ⟨y, by rw [hy]; exact hx⟩

theorem realFirstCoefficientOfPolynomial_normalized
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (F.realAdaptedPolynomialMap w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x)) =
      F.realNormalizedFirstCoefficientMap w x := by
  rw [F.realNormalizedFirstCoefficientMap_eq, ← F.realNormalizedRelativeInFirst_coe]
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w _

theorem realReducedRelativeCoefficient_of_polynomial (hw : ∀ i, 0 < w i)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w g).coord) :
    F.realReducedRelativeCoefficient w hw g =
      F.realFirstCoefficientOfPolynomial b ω hF w
        (F.realAdaptedPolynomialMap w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x)) := by
  rw [F.realFirstCoefficientOfPolynomial_normalized]
  exact (F.realReducedRelativeCoefficient_of_preimage w hw g x hx).symm

variable [Fintype σ]

include b ω hF in
theorem exists_real_normalizedRelative_preimage (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hzero : coefficients (normalizedShiftLog (s + 1) h (-e) (-m)
      (F.realAdaptedPolynomialMap (fun _ => 1) g.coord) -
        F.realAdaptedPolynomialMap (fun _ => 1) g.coord) 0 ∈ F.realification.layer 2) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1),
      F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
          F.realification.normalizedRelativeLog h e m
            (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) ∧
      F.realNormalizedFirstCoefficientMap (fun _ => 1) x =
        F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          F.realFirstCoefficientConstant (fun _ => 1) e -
          F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have hmem := F.realification.normalizedRelativeLog_mem h e m
    (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) hzero
  obtain ⟨x, hx⟩ := F.realNormalizedRelative_polynomial_surjective b ω hF (fun _ => 1) ⟨_, hmem⟩
  refine ⟨x, hx, ?_⟩
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => p.val) hx
  have he := F.realFirstCoefficientOfPolynomial_normalized b ω hF (fun _ => 1) x
  change F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
    (F.realification.normalizedRelativeLog h e m
      (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val at hc
  rw [hc] at he
  exact he.symm.trans (F.realFirstCoefficientOfPolynomial_normalizedRelativeLog b ω hF h e m g)

include b ω hF in
theorem real_normalized_square_coefficient_identity (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (Q : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1))
    (hQ : F.realReducedRelativeSquareSymbolMap (fun _ => 1) (fun _ => Nat.zero_lt_one) x =
      (F.reducedSquareRealRelativePart (fun _ => 1) Q).coord)
    (hx : F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
      F.realification.normalizedRelativeLog h e m (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)) :
    F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) =
      F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) Q := by
  rw [F.realReducedRelativeCoefficient_of_polynomial b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) Q x hQ]
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => p.val) hx
  change F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
    (F.realification.normalizedRelativeLog h e m
      (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val at hc
  rw [hc]
  exact (F.realFirstCoefficientOfPolynomial_normalizedRelativeLog b ω hF h e m g).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realSquareDiagonalPolynomialHom :
    F.RealAdaptedPolynomialGroup w →* F.squareFiltration.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.squareDiagonalPolynomialMap w)

noncomputable def realRelativeSquarePolynomial (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.squareFiltration.RealAdaptedPolynomialGroup w :=
  ⟨(F.relativeSquareLift w hw).baseChange ℝ x⟩

theorem realSquareFstPolynomialHom_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.realSquareFstPolynomialHom w (F.realSquareDiagonalPolynomialHom w g) = g := by
  have hcomp : (F.squareFstPolynomialMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact F.squareFstPolynomialMap_diagonal w p
  apply NilpotentLieBCHGroup.ext
  change (F.squareFstPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) = g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
    LinearMap.id_apply]

theorem realSquareSndPolynomialHom_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.realSquareSndPolynomialHom w (F.realSquareDiagonalPolynomialHom w g) = g := by
  have hcomp : (F.squareSndPolynomialMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact F.squareSndPolynomialMap_diagonal w p
  apply NilpotentLieBCHGroup.ext
  change (F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) = g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
    LinearMap.id_apply]

theorem realSquareFstPolynomialHom_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realSquareFstPolynomialHom w (F.realRelativeSquarePolynomial w hw x) =
      (⟨(F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x⟩ : F.RealAdaptedPolynomialGroup w) := by
  have hcomp : (F.squareFstPolynomialMap w).toLinearMap.comp (F.relativeSquareLift w hw) =
      (F.normalizedRelativeSubmodule w).subtype := by
    apply LinearMap.ext
    intro p
    exact F.squareFstPolynomialMap_relative w hw p
  apply NilpotentLieBCHGroup.ext
  change (F.squareFstPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

theorem realSquareSndPolynomialHom_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realSquareSndPolynomialHom w (F.realRelativeSquarePolynomial w hw x) = 1 := by
  have hcomp : (F.squareSndPolynomialMap w).toLinearMap.comp (F.relativeSquareLift w hw) = 0 := by
    apply LinearMap.ext
    intro p
    exact F.squareSndPolynomialMap_relative w hw p
  apply NilpotentLieBCHGroup.ext
  change (F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero,
    LinearMap.zero_apply]

theorem realSquarePolynomial_factorization (hw : ∀ i, 0 < w i)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hf : F.realSquareFstPolynomialHom w r =
      (⟨(F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x⟩ : F.RealAdaptedPolynomialGroup w) * g)
    (hs : F.realSquareSndPolynomialHom w r = g) :
    r = F.realRelativeSquarePolynomial w hw x * F.realSquareDiagonalPolynomialHom w g := by
  apply F.realSquarePolynomial_ext w
  · rw [map_mul, F.realSquareFstPolynomialHom_relative, F.realSquareFstPolynomialHom_diagonal, hf]
  · rw [map_mul, F.realSquareSndPolynomialHom_relative, F.realSquareSndPolynomialHom_diagonal, one_mul, hs]

theorem realSquareDifference_mem_two (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    realificationLieHom F.squareFst x - realificationLieHom F.squareSnd x ∈ F.realification.layer 2 := by
  rw [← F.realifiedSquareEquiv_fst, ← F.realifiedSquareEquiv_snd]
  exact (F.realification.mem_squareLieSubalgebra (F.realifiedSquareEquiv x).val).mp
    (F.realifiedSquareEquiv x).property

theorem realSquarePolynomial_horizontal (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord -
      F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord) 0 ∈ F.realification.layer 2 := by
  rw [map_sub, Finsupp.sub_apply, F.realSquareFstPolynomialHom_polynomial,
    F.realSquareSndPolynomialHom_polynomial, coefficients_map, coefficients_map]
  exact F.realSquareDifference_mem_two _

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem realAdaptedPolynomialGroupHom_injective :
    Function.Injective (F.realAdaptedPolynomialGroupHom w) := by
  intro g h hgh
  apply NilpotentLieBCHGroup.ext
  apply F.realAdaptedPolynomialTensor_injective b ω hF w
  exact congrArg NilpotentLieBCHGroup.coord hgh

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem nativeSquareOrbit_fst (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        F.realification.polynomialOrbitEval w x
          (F.nativePolynomialOrbit w (F.realSquareFstPolynomialHom w r)) := by
  apply NilpotentLieBCHGroup.ext
  have h := congrArg (eval (fun i => (x i : ℚ))) (F.realSquareFstPolynomialHom_polynomial w r)
  rw [eval_map] at h
  exact h.symm

theorem nativeSquareOrbit_snd (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (x : σ → ℤ) :
    F.realSquareSndHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        F.realification.polynomialOrbitEval w x
          (F.nativePolynomialOrbit w (F.realSquareSndPolynomialHom w r)) := by
  apply NilpotentLieBCHGroup.ext
  have h := congrArg (eval (fun i => (x i : ℚ))) (F.realSquareSndPolynomialHom_polynomial w r)
  rw [eval_map] at h
  exact h.symm

theorem nativeNormalizedSquareOrbit_fst (h : σ → ℤ) (ε γ : F.realification.Group)
    (g : F.RealAdaptedPolynomialGroup w) (r : F.squareFiltration.RealAdaptedPolynomialGroup w)
    (hf : F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      normalizedShiftLog s (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
        (F.realAdaptedPolynomialMap w g.coord)) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        ε⁻¹ * F.realification.polynomialOrbitEval w (fun i => x i + h i)
          (F.nativePolynomialOrbit w g) * γ⁻¹ := by
  rw [F.nativeSquareOrbit_fst, mul_assoc]
  apply NilpotentLieBCHGroup.ext
  have hh := congrArg (eval (fun i => (x i : ℚ))) hf
  rw [eval_normalizedShiftLog] at hh
  change eval (fun i => (x i : ℚ))
      (F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord) =
    lieBCH s (-ε.coord)
      (lieBCH s (eval (fun i => ((x i + h i : ℤ) : ℚ))
        (F.realAdaptedPolynomialMap w g.coord)) (-γ.coord))
  simpa only [Int.cast_add] using hh

theorem nativeNormalizedSquareObservable_product (Γ : Subgroup F.Group)
    (h : σ → ℤ) (ε γ : F.realification.Group)
    (hγ : γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom)
    (u : F.realification.Group ⧸ Γ.map NilpotentLieBCHGroup.realificationHom → ℂ)
    (g : F.RealAdaptedPolynomialGroup w) (r : F.squareFiltration.RealAdaptedPolynomialGroup w)
    (hf : F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      normalizedShiftLog s (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
        (F.realAdaptedPolynomialMap w g.coord))
    (hs : F.realSquareSndPolynomialHom w r = g) (x : σ → ℤ) :
    F.realSquareObservable Γ ε u
      (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x
        (F.squareFiltration.nativePolynomialOrbit w r))) =
      u (QuotientGroup.mk (F.realification.polynomialOrbitEval w (fun i => x i + h i)
        (F.nativePolynomialOrbit w g))) *
      star (u (QuotientGroup.mk (F.realification.polynomialOrbitEval w x
        (F.nativePolynomialOrbit w g)))) := by
  apply F.realSquareObservable_recovers_product Γ ε γ _ _ hγ u
  · exact F.nativeNormalizedSquareOrbit_fst w h ε γ g r hf x
  · rw [F.nativeSquareOrbit_snd, hs]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealNormalizedSquareFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem exists_real_normalized_square_factors (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-e) (-m) (F.realAdaptedPolynomialMap (fun _ => 1) g.coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) g.coord) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1),
      F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
          F.realification.normalizedRelativeLog h e m
            (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) ∧
      r = F.realRelativeSquarePolynomial (fun _ => 1) (fun _ => Nat.zero_lt_one) x *
        F.realSquareDiagonalPolynomialHom (fun _ => 1) g ∧
      F.realNormalizedFirstCoefficientMap (fun _ => 1) x =
        F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          F.realFirstCoefficientConstant (fun _ => 1) e -
          F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have hzero := F.realSquarePolynomial_horizontal (fun _ : σ => 1) r
  rw [hf, hs] at hzero
  obtain ⟨x, hx, hcoeff⟩ := F.exists_real_normalizedRelative_preimage b ω hF h e m g hzero
  let y : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) :=
    ⟨(F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x⟩
  have hshift : F.realAdaptedPolynomialTensor (fun _ => 1)
      (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        F.realification.normalizedShiftAdapted h (-e) (-m)
          (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) := Subtype.ext hf
  have hy : F.realAdaptedPolynomialGroupHom (fun _ => 1) y =
      F.realAdaptedPolynomialGroupHom (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r) *
        (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)⁻¹ := by
    apply NilpotentLieBCHGroup.ext
    change F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
      lieBCH (s + 1)
        (F.realAdaptedPolynomialTensor (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord)
        (-(F.realAdaptedPolynomialTensor (fun _ => 1) g.coord))
    rw [hshift]
    exact hx
  have hfirst : F.realSquareFstPolynomialHom (fun _ => 1) r = y * g := by
    apply F.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    rw [map_mul, hy]
    group
  have hsecond : F.realSquareSndPolynomialHom (fun _ => 1) r = g := by
    apply F.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    apply NilpotentLieBCHGroup.ext
    exact Subtype.ext hs
  exact ⟨x, hx, F.realSquarePolynomial_factorization (fun _ => 1)
    (fun _ => Nat.zero_lt_one) r g x hfirst hsecond, hcoeff⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedSquareMetric
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]

theorem realSquareObservable_lipschitz (e : Basis ι ℚ L) (b : Basis κ ℚ F.squareLieSubalgebra)
    (Γ : Subgroup F.Group) (l m H : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hSq : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid m)
    (hfst : ∀ k i, RationalHeightLE (e.repr (F.squareFst (b i)) k) H)
    (hsnd : ∀ k i, RationalHeightLE (e.repr (F.squareSnd (b i)) k) H)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (A K B : ℝ≥0)
    (hε : letI := realificationQuotientMetricSpace e Γ l hl hΓ
      LipschitzWith A (fun x : F.realification.Group ⧸ Γ.map realificationHom => ε • x))
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith K u)
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let P := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) H
    letI := realificationQuotientMetricSpace b (F.squareLattice Γ) m hm hSq
    LipschitzWith (B * (K * P) + B * (K * (A * P))) (F.realSquareObservable Γ ε u) := by
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  let := realificationQuotientMetricSpace b (F.squareLattice Γ) m hm hSq
  have hf := lipschitz_realificationMap_quotient b e F.squareFst (F.squareLattice Γ) Γ
    (F.squareLattice_le_fst Γ) m l hm hl hSq hΓ H hfst
  have hg := lipschitz_realificationMap_quotient b e F.squareSnd (F.squareLattice Γ) Γ
    (F.squareLattice_le_snd Γ) m l hm hl hSq hΓ H hsnd
  exact lipschitz_mul_star_of_bounds _ _ (hu.comp (hε.comp hf)) (hu.comp hg)
    (fun x => hb _) (fun x => hb _)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

@[simp] theorem productProjectionHom_pi_symm (g : ∀ i, (D i).RealGroup) (i : ι) :
    productProjectionHom D i ((realBCHPiEquiv (fun j => (D j).filtration)).symm g) = g i :=
  congrFun ((realBCHPiEquiv (fun j => (D j).filtration)).apply_symm_apply g) i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEqualDimension
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d k : ℕ}

def castDimension (D : RationalFilteredNilmanifold L s d) (h : d = k) :
    RationalFilteredNilmanifold L s k := h ▸ D

theorem castDimension_geometry (D : RationalFilteredNilmanifold L s d) (h : d = k) (p : ℝ) :
    (D.castDimension h).GeometryComplexityLE p ↔ D.GeometryComplexityLE p := by
  cases h
  rfl

namespace Niltest

variable {σ : Type*} {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def castDimension (T : D.Niltest w) (h : d = k) : (D.castDimension h).Niltest w := by
  cases h
  exact T

theorem castDimension_normBound (T : D.Niltest w) (h : d = k) :
    (T.castDimension h).normBound = T.normBound := by
  cases h
  rfl

theorem castDimension_eval (T : D.Niltest w) (h : d = k) (x : σ → ℤ) :
    (T.castDimension h).eval x = T.eval x := by
  cases h
  rfl

theorem castDimension_complexity (T : D.Niltest w) (h : d = k) (p : ℝ) :
    (T.castDimension h).ComplexityLE p ↔ T.ComplexityLE p := by
  cases h
  rfl

theorem castDimension_unit_interval (T : D.Niltest w) (h : d = k) :
    (T.castDimension h).UnitIntervalValued ↔ T.UnitIntervalValued := by
  cases h
  rfl

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SingleRefilteredKernel
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

noncomputable def refilteredComponentMap (b : ι) :
    ((pi D).filtration.gradedRefiltrationSubalgebra W) →ₗ⁅ℚ⁆ L b :=
  (liePiEval b).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl

noncomputable def nativeRefilteredTarget
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n) :=
  optionProduct (Q.raiseStep (Nat.le_succ s)) (fun i : {i : ι // i ≠ a} => D i.val)

noncomputable def nativeRefilteredMap :=
  optionProductMap (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
    (fun i : {i : ι // i ≠ a} => refilteredComponentMap D W i.val)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareRecovery
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Module

theorem bchSubgroup_inner_grid_of_reindex {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (b : Basis ι ℚ L) (e : ι ≃ κ) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {N : ℕ}
    (h : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (b.reindex e) Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ := by
  have hb : (b.reindex e).reindex e.symm = b := by
    ext i
    simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  have h' := bchSubgroup_inner_grid_reindex (b.reindex e) e.symm Γ h
  rwa [hb] at h'

namespace RationalFilteredNilmanifold

theorem exists_native_factorwise_covers :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ), 0 < m →
      (scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ) →
      ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
          ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
          ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        (pi E).GeometryComplexityLE ((p + C) ^ C) ∧ (pi E).lattice ≤ Λ := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2
  let P := 2 * X ^ 2 + Q + (Q + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ s d D Λ m hm hΛ p hp hι hD hmp
  have hraw : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis (fun i => (D i).basis)) Λ :=
    bchSubgroup_inner_grid_of_reindex _ (Fintype.equivFin _) Λ hΛ
  obtain ⟨Δ, N, hdata, hsubset⟩ := exists_factorwise_bch_covers
    (fun i => (D i).filtration) (fun i => (D i).basis) (fun i => (D i).lattice)
    (fun i => (D i).grid) (fun i => (D i).grid_pos) (fun i => (D i).inner_grid)
    (fun i => (D i).outer_grid) Λ m hm hraw hp
    (fun i => by simpa only [Fintype.card_fin] using (hD i).1) (fun i => (hD i).2.1) hmp
  have hN : ∀ i, 0 < N i := fun i => by rcases hdata i with ⟨_, _, _, _, _, h, _, _, _⟩; exact h
  have hNb : ∀ i, (N i : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, h, _, _⟩; exact h
  have hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, _, h, _⟩; exact h
  have hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, _, _, h⟩; exact h
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  have hpq : p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hE : ∀ i, (E i).GeometryComplexityLE ((p + 2) ^ 2) := fun i =>
    (D i).withLattice_geometry (Δ i) (N i) (hN i) (hin i) (hout i) (hD i) hpq (hNb i)
  have hprod := pi_geometry E (sq_nonneg (p + 2)) (hι.trans hpq) hE
  have hsum : 2 * p ^ 2 + (p + 2) ^ 2 + ((p + 2) ^ 2 + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, Q, X, Polynomial.eval₂_pow] using hbudget p hp
  have hidx : 2 * p ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (p + 2), sq_nonneg ((p + 2) ^ 2 + 2)]
  have hgeom : (p + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg p, sq_nonneg ((p + 2) ^ 2 + 2)]
  have hprodgeom : ((p + 2) ^ 2 + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg p, sq_nonneg (p + 2)]
  refine ⟨Δ, N, hN, hin, hout, ?_, fun i => (hE i).mono (E i) hgeom,
    hprod.mono (pi E) hprodgeom, hsubset⟩
  intro i
  rcases hdata i with ⟨hle, hchar, hnormal, hfinite, hindex, _, _, _, _⟩
  exact ⟨hle, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hidx)⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepOneSymbolLinearPart
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def stepOneFrequencyKernel (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ) :
    LieSubalgebra ℚ L :=
  { LinearMap.ker η with
    lie_mem' := fun {a b} _ _ => by
      change η ⁅a, b⁆ = 0
      rw [F.stepOne_lie_eq_zero, map_zero] }

theorem mem_real_stepOneFrequencyKernel (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ)
    (x : ℝ ⊗[ℚ] L) :
    x ∈ realificationLieSubalgebra (F.stepOneFrequencyKernel η) ↔ realifyFunctional η x = 0 :=
  mem_realified_frequency_kernel_iff η x

theorem exists_stepOne_linear_splitting {σ ι : Type*} [Fintype σ] [DecidableEq σ]
    (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)
    (η : L →ₗ[ℚ] ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] L)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (E P R : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      0 < m ∧ m ≤ H ∧ E * P * R = F.realification.linearPolynomialGroup a ∧
      F.PolynomialSlowBound b (fun _ => 1) (fun i => (T i : ℝ)) ((H : ℝ) / (2 * δ)) E ∧
      F.PolynomialRationalGrid b (fun _ => 1) m R ∧
      (∀ t : σ → ℝ, eval₂ t (P.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
        realificationLieSubalgebra (F.stepOneFrequencyKernel η)) ∧
      coefficients (P.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  obtain ⟨m, e, p, r, hm, hmH, hsum, hp, he, hr⟩ :=
    exists_linear_frequency_splitting b η hH hheight T hT a hδ hbias
  let E := F.realification.linearPolynomialGroup e
  let P := F.realification.linearPolynomialGroup p
  let R := F.realification.linearPolynomialGroup r
  refine ⟨m, E, P, R, hm, hmH, ?_, ?_, F.polynomialRationalGrid_linear b m r hr, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    rw [(F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).stepOne_coord_mul,
      (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).stepOne_coord_mul]
    apply Subtype.ext
    change linearPolynomial e + linearPolynomial p + linearPolynomial r = linearPolynomial a
    rw [← map_add, ← map_add]
    congr 1
    funext i
    exact hsum i
  · apply F.polynomialSlowBound_linear b (fun i => (T i : ℝ)) (fun i => Nat.cast_pos.mpr (hT i))
      (div_nonneg (Nat.cast_nonneg H) (by positivity))
    intro i j
    apply (he i j).trans_eq
    field_simp
  · intro t
    rw [F.mem_real_stepOneFrequencyKernel]
    change realifyFunctional η (eval₂ t (linearPolynomial p)) = 0
    simp only [eval₂_linearPolynomial, map_sum, map_smul, hp, smul_zero, Finset.sum_const_zero]
  · exact coefficients_linearPolynomial_zero p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)

theorem stepOne_basis_layers (j : ℕ) :
    F.layer j = Submodule.span ℚ (b '' {i | j ≤ (fun _ : ι => 1) i}) := by
  by_cases hj : j ≤ 1
  · have htop : F.layer j = ⊤ := top_unique (F.one_eq_top ▸ F.antitone hj)
    simpa only [hj, Set.ofPred_true, Set.image_univ, b.span_eq] using htop
  · have hbot : F.layer j = ⊥ := bot_unique ((F.antitone (by omega : 2 ≤ j)).trans F.terminal.le)
    simpa only [hj, Set.ofPred_false, Set.image_empty, Submodule.span_empty] using hbot

variable (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include F b hlayers in
theorem stepOne_basis_weight (i : ι) : ω i = 1 := by
  have hpos := F.adaptedBasis_weight_pos b ω hlayers i
  have hle := F.adaptedBasis_weight_le_step b ω hlayers i
  omega

noncomputable def stepOneGradedEquiv : L ≃ₗ⁅ℚ⁆ F.AssociatedGraded :=
  { b.repr.trans (F.associatedGradedBasis b ω hlayers).repr.symm with
  map_lie' {x y} := by
    rw [F.stepOne_lie_eq_zero, F.associatedGradedFiltration.stepOne_lie_eq_zero]
    exact map_zero (b.repr.trans (F.associatedGradedBasis b ω hlayers).repr.symm) }

@[simp] theorem stepOneGradedEquiv_coordinate (x : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.stepOneGradedEquiv b ω hlayers x) i =
      b.repr x i := by
  change (F.associatedGradedBasis b ω hlayers).repr
    ((F.associatedGradedBasis b ω hlayers).repr.symm (b.repr x)) i = _
  rw [LinearEquiv.apply_symm_apply]

theorem stepOne_gradedPieceProjection (j : ℕ) (x : L) :
    F.gradedPieceProjection b ω hlayers j x =
      if j = 1 then F.stepOneGradedEquiv b ω hlayers x else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.stepOne_basis_weight b ω hlayers i]
  by_cases hj : j = 1
  · simp only [hj, ite_true, F.stepOneGradedEquiv_coordinate]
  · simp only [hj, Ne.symm hj, ite_false, map_zero, Finsupp.zero_apply]

theorem stepOne_graded_submodule (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U := by
  intro j x hx
  have he : basisGradeProjection (F.associatedGradedBasis b ω hlayers) ω j x =
      if j = 1 then x else 0 := by
    classical
    apply (F.associatedGradedBasis b ω hlayers).repr.injective
    ext i
    rw [basisGradeProjection_repr, F.stepOne_basis_weight b ω hlayers i]
    by_cases hj : j = 1
    · simp only [hj, ite_true]
    · simp only [hj, Ne.symm hj, ite_false, map_zero, Finsupp.zero_apply]
  rw [he]
  split_ifs
  · exact hx
  · exact U.zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1)

theorem stepOne_symbol_linearPart (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.polynomialSymbolMap (fun _ => 1)
      (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord =
      F.polynomialSymbolMap (fun _ => 1) p := by
  have hp : DegreeLE (fun _ : σ => 1) 1 p.val :=
    F.adapted_degreeLE _ ((F.mem_adaptedSubmodule _ _).mp p.property)
  have he : F.adaptedConstant (fun _ : σ => 1) (coefficients p.val 0) +
      (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord = p := by
    apply Subtype.ext
    exact (eq_affine_of_degreeLE_one p.val hp).symm
  calc
    _ = F.polynomialSymbolMap (fun _ : σ => 1)
        (F.adaptedConstant (fun _ : σ => 1) (coefficients p.val 0) +
          (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord) := by
      rw [map_add, F.polynomialSymbolMap_constant, zero_add]
    _ = _ := congrArg (F.polynomialSymbolMap (fun _ : σ => 1)) he

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StepOneGradedKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def stepOneGradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (F.stepOneGradedEquiv b ω hlayers).symm.toLinearEquiv.toLinearMap

@[simp] theorem stepOneGradedFrequency_equiv (η : L →ₗ[ℚ] ℚ) (x : L) :
    F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = η x := by
  change η ((F.stepOneGradedEquiv b ω hlayers).symm (F.stepOneGradedEquiv b ω hlayers x)) = _
  rw [LieEquiv.symm_apply_apply]

noncomputable def stepOneGradedKernel (η : L →ₗ[ℚ] ℚ) : LieSubalgebra ℚ F.AssociatedGraded :=
  F.associatedGradedFiltration.stepOneFrequencyKernel (F.stepOneGradedFrequency b ω hlayers η)

theorem mem_stepOneGradedKernel (η : L →ₗ[ℚ] ℚ) (x : F.AssociatedGraded) :
    x ∈ F.stepOneGradedKernel b ω hlayers η ↔ F.stepOneGradedFrequency b ω hlayers η x = 0 := Iff.rfl

theorem stepOneGradedKernel_span {κ : Type*} (η : L →ₗ[ℚ] ℚ) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = (F.stepOneFrequencyKernel η).toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.stepOneGradedEquiv b ω hlayers (v i))) =
      (F.stepOneGradedKernel b ω hlayers η).toSubmodule := by
  have hmap : (F.stepOneFrequencyKernel η).toSubmodule.map
      (F.stepOneGradedEquiv b ω hlayers).toLinearEquiv.toLinearMap =
      (F.stepOneGradedKernel b ω hlayers η).toSubmodule := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = 0
      rw [F.stepOneGradedFrequency_equiv]
      exact hx
    · intro hy
      refine ⟨(F.stepOneGradedEquiv b ω hlayers).symm y, hy, ?_⟩
      exact (F.stepOneGradedEquiv b ω hlayers).apply_symm_apply y
  calc
    _ = (Submodule.span ℚ (Set.range v)).map
        (F.stepOneGradedEquiv b ω hlayers).toLinearEquiv.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = _ := by rw [hv, hmap]

theorem stepOne_gradedPieceProjection_mem_kernel (η : L →ₗ[ℚ] ℚ) (j : ℕ)
    {x : L} (hx : x ∈ F.stepOneFrequencyKernel η) :
    F.gradedPieceProjection b ω hlayers j x ∈ F.stepOneGradedKernel b ω hlayers η := by
  rw [F.stepOne_gradedPieceProjection]
  split_ifs
  · change F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = 0
    rw [F.stepOneGradedFrequency_equiv]
    exact hx
  · exact (F.stepOneGradedKernel b ω hlayers η).zero_mem

theorem stepOne_symbol_values_in_gradedKernel (η : L →ₗ[ℚ] ℚ)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ t : σ → ℝ, eval₂ t p ∈ realificationLieSubalgebra (F.stepOneFrequencyKernel η)) :
    ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) ∈
        realificationLieSubalgebra (F.stepOneGradedKernel b ω hlayers η) := by
  have hc := (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.stepOneFrequencyKernel η)).toSubmodule p).mp hp
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.stepOneGradedKernel b ω hlayers η)).toSubmodule _).mpr
  intro α
  rw [F.realGradedSymbolPolynomial_coefficient_of_polynomial]
  exact baseChange_mem_of_mapsTo (F.stepOneFrequencyKernel η).toSubmodule
    (F.stepOneGradedKernel b ω hlayers η).toSubmodule
    (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α))
    (fun _ hx => F.stepOne_gradedPieceProjection_mem_kernel b ω hlayers η _ hx) (hc α)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_sub_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ξ η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (ξ - η) x = realifyFunctional ξ x - realifyFunctional η x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t v => simp only [realifyFunctional_tmul, LinearMap.sub_apply, Rat.cast_sub, mul_sub]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

theorem realifyFunctional_eq_on_submodule {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℚ V) (ξ η : V →ₗ[ℚ] ℚ) (h : ∀ x ∈ P, ξ x = η x)
    (x : ℝ ⊗[ℚ] V) (hx : x ∈ P.baseChange ℝ) :
    realifyFunctional ξ x = realifyFunctional η x := by
  have hker : P ≤ LinearMap.ker (ξ - η) := by
    intro y hy
    change ξ y - η y = 0
    exact sub_eq_zero.mpr (h y hy)
  have hz := (mem_realified_frequency_kernel_iff (ξ - η) x).mp (Submodule.baseChange_mono ℝ hker hx)
  rw [realifyFunctional_sub_apply] at hz
  exact sub_eq_zero.mp hz

namespace NilpotentLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_refiltered_lieTreeEval_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (d : I → ℕ) (v : I → ℝ ⊗[ℚ] L) (hv : ∀ i, v i ∈ F.realGradedRefiltrationLayer U (d i))
    (a : FreeMagma I) : lieTreeEval v a ∈ F.realGradedRefiltrationLayer U (lieTreeWeight d a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.realGradedRefiltrationLayer_lie_mem U ha hb

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem real_refiltered_rank_bracket_frequency (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ξ η : L →ₗ[ℚ] ℚ)
    (hξ : ∀ x ∈ U,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω s x = x →
        D.filtration.gradedFrequency b ω hF ξ x = 0)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : I → ℝ ⊗[ℚ] L) (hv : ∀ i, v i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) :
    realifyFunctional η (lieTreeEval v a) = 0 := by
  have htop : lieTreeEval v a ∈ D.filtration.realGradedRefiltrationLayer U s := by
    simpa only [hd] using D.filtration.real_refiltered_lieTreeEval_mem U d v hv a
  have hleaves (i : I) : v i ∈ R.filtration.realification.layer (d i) 1 := by
    have h : v i ∈ D.filtration.realification.layer (d i) :=
      D.filtration.realGradedRefiltrationLayer_le U (d i) (hv i)
    rw [← R.real_associated] at h
    change v i ∈ R.filtration.realification.layer (d i) 0 at h
    rwa [R.filtration.realification.rank_zero_eq_one] at h
  have hrank : lieTreeEval v a ∈ (R.filtration.layer s r).baseChange ℝ := by
    have h : lieTreeEval v a ∈ R.filtration.realification.layer s r := by
      simpa only [hd, hr] using R.filtration.realification.lieTreeEval_mem_length v d hleaves a
    exact h
  rw [← realifyFunctional_eq_on_submodule (R.filtration.layer s r) ξ η hrestrict _ hrank]
  exact D.filtration.real_frequency_zero_on_refiltered_top b ω hF U ξ hξ _ htop

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

def ControlledRankBracketFactorization (_R : D.DegreeRankStructure r) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (A P B : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : Fin n → D.filtration.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ A * P * B = X ∧
    D.filtration.SymbolSlowBound D.basis ω hF (fun _ => 1) T (Real.exp p) A ∧
    D.filtration.SymbolRationalGrid D.basis ω hF (fun _ => 1) m B ∧
    Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
    (∀ (k : ℕ) (d : Fin k → ℕ) (a : FreeMagma (Fin k)),
      lieTreeWeight d a = s → a.length = r →
      ∀ u : Fin k → ℝ ⊗[ℚ] L,
        (∀ i, u i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) →
        realifyFunctional η (lieTreeEval u a) = 0) ∧
    P.coord ∈ realificationLieSubalgebra (D.filtration.symbolPointwiseSubalgebra D.basis ω hF (fun _ => 1) U)

theorem controlledRankBracketFactorization_of_frequency_restriction (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (ξ η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (h : D.filtration.ControlledSymbolFactorization D.basis ω hF ξ T X p)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x) :
    R.ControlledRankBracketFactorization ω hF η T X p := by
  obtain ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hheight, hξ, hP⟩ := h
  refine ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hheight, ?_, hP⟩
  intro k d a hd hr u hu
  exact R.real_refiltered_rank_bracket_frequency D.basis ω hF U ξ η hξ hrestrict d a hd hr u hu

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)
  (ω : Fin n → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

theorem ControlledRankBracketFactorization.exists_in {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : R.ControlledRankBracketFactorization ω hF η T X p) :
    ∃ (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : Fin n → D.filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
      (∀ (k : ℕ) (d : Fin k → ℕ) (a : FreeMagma (Fin k)),
        lieTreeWeight d a = s → a.length = r → ∀ u : Fin k → ℝ ⊗[ℚ] L,
        (∀ i, u i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) →
        realifyFunctional η (lieTreeEval u a) = 0) ∧
      D.filtration.SymbolFactorizationIn D.basis ω hF T X p l U := by
  obtain ⟨l, A, P, B, U, v, hl, hlp, hprod, hA, hB, hv, hU, hh, hker, hP⟩ := h
  exact ⟨l, U, v, hl, hlp, hv, hU, hh, hker, A, P, B, hprod, hA, hB, hP⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)
  (ω : Fin n → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

theorem ControlledRankBracketFactorization.mono {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : R.ControlledRankBracketFactorization ω hF η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : R.ControlledRankBracketFactorization ω hF η T X q := by
  obtain ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hh, hη, hP⟩ := h
  exact ⟨m, A, P, B, U, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    D.filtration.symbolSlowBound_mono D.basis ω hF (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) A hA,
    hB, hv, hU, (fun i j => (hh i j).trans hpq), hη, hP⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerOrbitTranslation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

@[simp] theorem integerOrbitPoint_translate
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (c n : ℤ) :
    D.integerOrbitPoint (g.translate (fun _ => Nat.zero_lt_one) (fun _ => c)) n =
      D.integerOrbitPoint g (n + c) := by
  unfold integerOrbitPoint
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedSquareImagePartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def SquareImageRecoverySpec (s t k C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d dV dQ : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV)
      (Q : RationalFilteredNilmanifold M t dQ)
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M) {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
        (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
        (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
        let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
        (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
          ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
          ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
        letI := Q.metricSpace
        let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
        ∀ ε γ : D.RealGroup, γ ∈ D.realLattice →
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ∀ a b c d : D.RealGroup, ∀ u v : D.filtration.squareFiltration.realification.Group,
            D.filtration.realSquareFstHom u = ε⁻¹ * a * γ⁻¹ →
            D.filtration.realSquareSndHom u = b →
            D.filtration.realSquareFstHom v = ε⁻¹ * c * γ⁻¹ →
            D.filtration.realSquareSndHom v = d →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk a : (E true).Space) (QuotientGroup.mk c) ≤ ρ →
              dist (QuotientGroup.mk b : (E false).Space) (QuotientGroup.mk d) ≤ ρ →
              dist (QuotientGroup.mk (ψ u) : Q.Space) (QuotientGroup.mk (ψ v)) ≤
                Real.exp ((p + C) ^ C) * ρ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def PrescribedSquareImagePartitionSpec (s t k₀ a C : ℕ) : Prop :=
    ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d dV dQ : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV)
      (Q : RationalFilteredNilmanifold M t dQ)
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      1 ≤ s → 2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 1 / δ ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
          (Fintype.card ((Fin n × ZMod q) × Fin k) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((Fin n × ZMod q) × Fin k) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ δ) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h δ).card : ℝ) / N ≤ 6 * δ + 3 / N) ∧
            letI := Q.metricSpace
            let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
              (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
            ∀ (h : ZMod N) (branch : Fin 2) (η γ : D.RealGroup)
              (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                γ ∈ D.realLattice →
                (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + 2) ^ k₀)) →
                (∀ z : Unit → ℤ,
                  D.filtration.realSquareFstHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      η⁻¹ * D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g * γ⁻¹ ∧
                  D.filtration.realSquareSndHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => c) g) →
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) rSq)) : Q.Space)
                    (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) rSq))) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

def CyclicShiftComparison.{u} (degree : ℕ) (epsilon : ℝ) (c : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p → Odd N →
    Real.exp ((p + 2) ^ c) ≤ N → ∀ f g J : ZMod N → ℝ,
    (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
    (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
    (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
    CyclicNiltestUpperComparison.{u} degree N ((p + 2) ^ c)
      (Real.exp (-((p + 2) ^ c))) f g →
    ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
      CyclicNiltestShiftBound.{u} (degree - 1) N p (Real.exp (-p))
        (fun n => f n - (1 + epsilon) * g n) J E

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

section

universe u v

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

universe u v

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.PositiveShiftBasis

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparationSliceComposition
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

@[simp] theorem identity_point (x : ∀ i, Fin (N i)) : (identity N).point x = x := by
  ext i
  simp [identity, point]

noncomputable def integerPolynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℤ :=
  MvPolynomial.C (S.start i : ℤ) + MvPolynomial.C (q : ℤ) * MvPolynomial.X i

@[simp] theorem integerPolynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℤ) (fun i => ((x i).val : ℤ)) (S.integerPolynomial i) =
      ((S.point x i).val : ℤ) := by
  simp [integerPolynomial, point, Nat.cast_add, Nat.cast_mul]

noncomputable def reindexInteger (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ) : MvPolynomial I ℤ :=
  MvPolynomial.aeval (R := ℤ) S.integerPolynomial P

@[simp] theorem reindexInteger_eval (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ)
    (x : ∀ i, Fin (S.length i)) :
    MvPolynomial.eval (fun i => ((x i).val : ℤ)) (S.reindexInteger P) =
      MvPolynomial.eval (fun i => ((S.point x i).val : ℤ)) P := by
  change MvPolynomial.aeval (R := ℤ) (fun i => ((x i).val : ℤ))
    (MvPolynomial.aeval (R := ℤ) S.integerPolynomial P) = _
  rw [MvPolynomial.comp_aeval_apply]
  simp only [integerPolynomial_eval, MvPolynomial.aeval_eq_eval]

end ResidueBoxSlice

namespace RankPreparationFamily

end RankPreparationFamily
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveScoreComparison
namespace OAI

section

universe u

namespace Erdos3

open scoped BigOperators TensorProduct

theorem CyclicNiltestUpperComparison.normalize {degree N : ℕ} [NeZero N]
    {P epsilon alpha c : ℝ} {f : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N P epsilon f (fun _ => c * alpha))
    (halpha : 0 < alpha) :
    CyclicNiltestUpperComparison.{u} degree N P (epsilon / alpha)
      (fun x => f x / alpha) (fun _ => c) := by
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  have he (x : ZMod N) : (f x / alpha - c) * (T.evalCyclic N (fun _ => x)).re =
      ((f x - c * alpha) * (T.evalCyclic N (fun _ => x)).re) / alpha := by
    field_simp [halpha.ne']
  simp only [he, ← Finset.expect_div]
  exact div_le_div_of_nonneg_right (h D hs T hT hTc) halpha.le

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedNaturalCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "radius" => blockJetScaleBound (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "height" => basisAxisScale (basis j) i
local notation "torus" => blockTorusFactor (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

noncomputable def allocatedSlicedGridPointCap (δ P : ℝ) (T d : ℕ) : ℝ :=
  max 1 (max ((allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ^ d)
    (max
      (positiveModerateSpectrumCardBudget j.val d ((layerTailDegree m + 1) * d) P
        (((torusA : ℝ) / (2 * gamma)) / δ ^ degree) ((torusA : ℝ) ^ d / δ ^ ((layerTailDegree m + 1) * d)) 1 + 1)
      (uniformSpectrumAbsoluteCap j.val d (degree * d) P
        ((torusI : ℝ) * cost / δ ^ degree) (((torusI : ℝ) * cost) ^ d / δ ^ (degree * d)))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastSpatialOutputHom {R : Type*} [AddCommMonoid R] :
    (X → R) →+ (Sigma (AllocatedCongruenceRankOutput X E inactive) → R) where
  toFun u o := match o.2 with
    | .inl x => u x.val
    | .inr _ => 0
  map_zero' := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> rfl
  map_add' u v := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> simp

def forecastCoefficientOutputHom {R : Type*} [AddCommMonoid R] :
    (∀ j, Fin (n j) ⊕ E j → R) →+
      (Sigma (AllocatedCongruenceRankOutput X E inactive) → R) where
  toFun label o := match o.2 with
    | .inl _ => 0
    | .inr (.inl i) => label o.1 (.inr i)
    | .inr (.inr a) => label o.1 (.inl a.val)
  map_zero' := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> rfl
  map_add' u v := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> simp

def forecastCongruenceOutput {R : Type*} (u : X → R)
    (label : ∀ j, Fin (n j) ⊕ E j → R) :
    Sigma (AllocatedCongruenceRankOutput X E inactive) → R := fun o =>
  match o.2 with
  | .inl x => u x.val
  | .inr (.inl i) => label o.1 (.inr i)
  | .inr (.inr a) => label o.1 (.inl a.val)

variable [Fintype X] [∀ j, Fintype (E j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [fintypeSigma : Fintype σ]

noncomputable def weightedBaseLinear (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ[ℚ] (σ → ℚ) :=
  baseLinear.comp (weightedSubalgebra w d).subtype

@[simp] theorem weightedBaseLinear_apply (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) : weightedBaseLinear w d x = x.val.base := rfl

theorem base_gradeProjection (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (j : ℕ) (x : weightedSubalgebra w d) :
    weightedBaseLinear w d
      (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x) =
      basisGradeProjection (Pi.basisFun ℚ σ) w j (weightedBaseLinear w d x) := by
  funext i
  rw [weightedBaseLinear_apply, weightedBasis_projection_base]
  have h := basisGradeProjection_repr (Pi.basisFun ℚ σ) w j x.val.base i
  simpa only [Pi.basisFun_repr, weightedBaseLinear_apply] using h.symm

theorem basisGradedSubmodule_ambient_base_image (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype)) :
    BasisGradedSubmodule (Pi.basisFun ℚ σ) w (U.map baseLinear) := by
  intro j b hb
  obtain ⟨x, hx, rfl⟩ := hb
  let y : weightedSubalgebra w d := ⟨x, hU hx⟩
  let z := basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j y
  have hz : z.val ∈ U := hgraded j y hx
  refine ⟨z.val, hz, ?_⟩
  exact base_gradeProjection w d hw j y

noncomputable def submoduleBasisCoordinates {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) : (τ → ℚ) →ₗ[ℚ] (σ → ℚ) :=
  K.subtype.comp b.equivFun.symm.toLinearMap

omit fintypeSigma in
theorem submoduleBasisCoordinates_injective [Fintype σ] {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) :
    Function.Injective (submoduleBasisCoordinates K b) :=
  Subtype.val_injective.comp b.equivFun.symm.injective

omit fintypeSigma in
@[simp] theorem submoduleBasisCoordinates_range [Fintype σ] {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) :
    (submoduleBasisCoordinates K b).range = K := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (b.equivFun.symm z).property
  · intro hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
    rw [b.equivFun.symm_apply_apply]

omit fintypeSigma in
@[simp] theorem submoduleBasisCoordinates_single [Fintype σ] {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) (j : τ) :
    submoduleBasisCoordinates K b (Pi.single j 1) = (b j).val := by
  change (b.equivFun.symm (Pi.single j 1)).val = _
  rw [b.equivFun_symm_apply]
  simp [Pi.single_apply]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped BigOperators

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_basisGraded_coordinate_basis (w : σ → ℕ)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K)
    (g : J → (σ → ℚ)) (hspan : Submodule.span ℚ (Set.range g) = K)
    {H : ℕ} (hH : 1 ≤ H) (hentries : ∀ j i, RationalHeightLE (g j i) H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (b : Basis (Fin n) ℚ K),
      (∀ j, v j ∈ Set.range w) ∧
      (∀ j i, v j ≠ w i → (b j).val i = 0) ∧
      (∀ j i, RationalHeightLE ((b j).val i) H) ∧
      ∀ j, ∃ a : J, (b j).val =
        basisGradeProjection (Pi.basisFun ℚ σ) w (v j) (g a) := by
  classical
  have hgm : ∀ a, g a ∈ K := by
    intro a
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  let S : Set K := {x | ∃ a : J, ∃ j ∈ Set.range w,
    x.val = basisGradeProjection (Pi.basisFun ℚ σ) w j (g a)}
  have hspanK : Submodule.span ℚ (Set.range (fun a => (⟨g a, hgm a⟩ : K))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff K hgm).mpr hspan
  have hS : ⊤ ≤ Submodule.span ℚ S := by
    rw [← hspanK]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let y (j : ℕ) : K := ⟨basisGradeProjection (Pi.basisFun ℚ σ) w j (g a),
      hK j (g a) (hgm a)⟩
    have hsum : ∑ j ∈ Finset.univ.image w, y j = (⟨g a, hgm a⟩ : K) := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using sum_basisGradeProjection_pi w (g a)
    change (⟨g a, hgm a⟩ : K) ∈ Submodule.span ℚ S
    rw [← hsum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    refine ⟨a, j, ?_, rfl⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, hi⟩
  let B := Basis.ofSpan hS
  let := FiniteDimensional.fintypeBasisIndex B
  let b := B.reindex (Fintype.equivFin _)
  have hb : ∀ j, b j ∈ S := by
    intro j
    dsimp only [b]
    rw [Basis.reindex_apply]
    exact Basis.ofSpan_subset hS ⟨_, rfl⟩
  choose a v hv hproj using hb
  refine ⟨_, v, b, hv, ?_, ?_, fun j => ⟨a j, hproj j⟩⟩
  · intro j i hji
    rw [hproj j, basisGradeProjection_pi_apply, if_neg (Ne.symm hji)]
  · intro j i
    rw [hproj j, basisGradeProjection_pi_apply]
    split_ifs
    · exact hentries (a j) i
    · simpa [RationalHeightLE] using hH

namespace PolynomialTranslationLie

theorem exists_controlled_graded_base_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K)
    (g : J → (σ → ℚ)) (hspan : Submodule.span ℚ (Set.range g) = K)
    {H : ℕ} (hH : 1 ≤ H) (hentries : ∀ j i, RationalHeightLE (g j i) H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ)),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = K ∧
      (∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) ∧
      (∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) ∧
      ∀ j, ∃ a : J, A (Pi.single j 1) =
        basisGradeProjection (Pi.basisFun ℚ σ) w (v j) (g a) := by
  obtain ⟨n, v, b, hv, hcoord, hheight, hselected⟩ :=
    exists_controlled_basisGraded_coordinate_basis w K hK g hspan hH hentries
  refine ⟨n, v, submoduleBasisCoordinates K b, ?_, ?_, ?_,
    submoduleBasisCoordinates_injective K b, submoduleBasisCoordinates_range K b,
    ?_, ?_, ?_⟩
  · have hn : Module.finrank ℚ K = n := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
    rw [← hn]
    simpa only [Module.finrank_pi] using Submodule.finrank_le K
  · intro j
    obtain ⟨i, hi⟩ := hv j
    simpa only [← hi] using hw i
  · intro j
    obtain ⟨i, hi⟩ := hv j
    simpa only [← hi] using hwd i
  · intro j i hji
    rw [submoduleBasisCoordinates_single]
    exact hcoord j i hji
  · intro j i
    rw [submoduleBasisCoordinates_single]
    exact hheight j i
  · intro j
    rw [submoduleBasisCoordinates_single]
    exact hselected j

end PolynomialTranslationLie

end Erdos3

end

end OAI

end


