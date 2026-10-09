-- Prove2me | Definitions.Def_OAIErdos3B042
-- name    : OAIErdos3B042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T06:26:19.179143+00:00
-- url     : https://prove2.me/theorems/528a0c9f-39fc-4cc1-b29d-af7b9d9aaf20
-- title:
--   OpenAI Erdős-3 split, definitions bundle 43 of 132
-- statement:
--   Definitions bundle 43 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B041`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 43 available.
--
--   Modules: `OAI.Erdos3.NativeCorrelationStructure.exists_rank_approximation_correlation`, `OAI.Erdos3.NativeCorrelationStructure.replaceRank`, `OAI.Erdos3.NativeCorrelationStructure.replacedRankResidual`, `OAI.Erdos3.NativeCorrelationStructure.replacedRankResidual_norm_sub_le`, `OAI.Erdos3.NativeCorrelationStructure.replacementFamily`, `OAI.Erdos3.NativeCorrelationStructure.selectedLower`, `OAI.Erdos3.NativeCorrelationStructure.selectedMixed`, `OAI.Erdos3.NativeCorrelationStructure.selectedProduct_eq`, `OAI.Erdos3.NativeCorrelationStructure.selectedRank`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_id_eq_changeStep`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_projection_height`, `OAI.Erdos3.NilpotentLieFiltration.exists_correlating_square_vertical_mode`, `OAI.Erdos3.NilpotentLieFiltration.exists_weights_of_tails`, `OAI.Erdos3.NilpotentLieFiltration.quotientFinBasis_projection_height`, `OAI.Erdos3.NilpotentLieFiltration.quotientFinBasis_repr_mk`, `OAI.Erdos3.NilpotentLieFiltration.squareFinBasis_projection_height`, `OAI.Erdos3.NilpotentLieFiltration.topQuotientModel`, `OAI.Erdos3.NilpotentLieFiltration.topQuotientModel_basis_layers`, `OAI.Erdos3.NilpotentLieFiltration.topQuotientModel_filtration`, `OAI.Erdos3.NilpotentLieFiltration.topQuotientModel_geometry`, `OAI.Erdos3.NilpotentLieFiltration.topQuotientModel_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.AllocatedMarkedDiagramRecoveryCovers`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData.casesOn`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData.exists_lower_rank_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData.model`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData.model_geometry_of_bounds`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData.rank`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData.rank_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_bounded_rank_adapted_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_controlled_lower_rank_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_controlled_rank_adapted_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_rank_adapted_data`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.rankFlag_span_height`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.rankQuotientOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.rankQuotientOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.terminal_le_topRankIdeal`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedNativeSquareFactors`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeBiasedSquareInModel`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.factorization`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeFactoredSquareInModel`, `OAI.Erdos3.RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.exists_fixed`, `OAI.Erdos3.RationalFilteredNilmanifold.LowerRefilteredCyclicExpansionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.LowerRefilteredRecoveryFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeGridRightDictionary.markedTopQuotient_recovery`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_correlating_vertical_mode`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_correlating_vertical_mode_preserving_characters`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_detection_vertical_mode`, `OAI.Erdos3.RationalFilteredNilmanifold.RefilteredRecoveryFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.conjugationPullback`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_allocated_marked_diagram_recovery_covers`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_native_square_factors`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_reduced_square_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_top_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_top_subspace_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_lowered_split_reconstruction_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_positive_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_partition_orbit_freezing`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_positive_frozen_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_shared_frozen_unit_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_split_reconstruction_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_topInvariant_integer_expansion`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_conjugated_source_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_frozen_coset_map`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_frozen_descent`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_frozen_map`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_frozen_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_frozen_two_target_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_native_positive_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_positive_frozen_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_unit_frozen_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.frozenCyclicOrbitValue`, `OAI.Erdos3.RationalFilteredNilmanifold.lipschitz_native_frozenCosetMap`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCoverMap`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCoverMap_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCoverMap_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCoverPullback`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCoverPullback_bounds`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCoverPullback_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.real_conjugationPullback_property`, `OAI.Erdos3.RationalFilteredNilmanifold.realificationMap_id_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.stepOne_controlled_symbol_factorization`, `OAI.Erdos3.RationalFilteredNilmanifold.topInvariantIntegerExponent`, `OAI.Erdos3.RationalFilteredNilmanifold.topInvariant_integer_expansion`, `OAI.Erdos3.TranslatedStepDropSpec`, `OAI.Erdos3.basisOfTail`, `OAI.Erdos3.basisOfTail_height`, `OAI.Erdos3.exists_coordinate_quotient_layer_basis`, `OAI.Erdos3.exists_many_biased_box_shifts`, `OAI.Erdos3.exists_native_frozen_rank_correlation`, `OAI.Erdos3.exists_native_shared_frozen_correlations`, `OAI.Erdos3.finiteCorrelation_one_derivative`, `OAI.Erdos3.norm_finiteCorrelation_one`, `OAI.Erdos3.tail_span_basis_members`, `OAI.Erdos3.translatedStepDropSpec_one`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B115

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFixedFactoredQuadruples
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedMixed (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x)

noncomputable def selectedRank (h : W.shifts) (x : ZMod N) : ℂ :=
  W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x

noncomputable def selectedLower (h : W.shifts) (x : ZMod N) : ℂ :=
  (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_eq (h : W.shifts) (x : ZMod N) :
    W.selectedProduct h x = W.selectedMixed h x * W.selectedRank h x * W.selectedLower h x := rfl

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

end Erdos3.NativeCorrelationStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePartitionFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d N : ℕ} [NeZero N]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def frozenCyclicOrbitValue (D : RationalFilteredNilmanifold L s d)
    (Φ : D.Space → ℂ) (ε b γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (y x : ZMod N) : ℂ :=
  Φ (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) ε *
     D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) b *
     D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) γ))

theorem exists_partition_orbit_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N M : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d)
      {p ρ : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      ∀ (A : I → ZMod N → ℝ), (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
      (∀ j x y, x ∉ cyclicWrapExceptional 0 ρ → y ∉ cyclicWrapExceptional 0 ρ →
        0 < A j x → 0 < A j y →
        |(x.val : ℝ) - y.val| ≤ N * ρ ∧ (M : ℤ) ∣ (x.val : ℤ) - y.val) →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ε * b * γ = g →
      CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((p + 2) ^ a)) ε.log →
      (∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y γ)) →
      ∃ y : I → ZMod N,
        (∀ j x, ‖D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖ ≤ 1) ∧
        (𝔼 x, ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)) -
          ∑ j, (A j x : ℂ) * D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖) ≤
            Real.exp ((p + C) ^ C) * ρ + 12 * ρ + 6 / N := by
  obtain ⟨C, hC, hfreeze⟩ := exists_orbit_factor_freezing s a
  refine ⟨C, hC, ?_⟩
  intro I L _ _ _ _ _ _ _ d N M _ D p ρ hp hD hρ A hA hsum hcells Φ K hΦ hLip hK ε b γ g hprod hε hperiod
  classical
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hchoose (j : I) : ∃ y : ZMod N, ∀ x, x ∉ E → 0 < A j x → y ∉ E ∧ 0 < A j y := by
    by_cases h : ∃ y, y ∉ E ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun _ _ => hΦ _, ?_⟩
  have hpoint (j : I) (x : ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)) -
        D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖ ≤ Real.exp ((p + C) ^ C) * ρ := by
    obtain ⟨hyE, hAy⟩ := hy j x hx hAx
    obtain ⟨hnear, hres⟩ := hcells j x (y j) hx hyE hAx hAy
    apply hfreeze D (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p (by linarith) hD
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp)
      Φ K hΦ hLip hK ε b γ g hprod (fun _ : Unit => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) hε
      (fun _ => (x.val : ℤ)) (fun _ => ((y j).val : ℤ)) ρ hρ.le
      (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (hperiod _ _ (fun _ => hres))
    · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using
        (Nat.cast_le.mpr x.val_lt.le : (x.val : ℝ) ≤ N)
    · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (y j).val from Nat.cast_nonneg _)] using
        (Nat.cast_le.mpr (y j).val_lt.le : ((y j).val : ℝ) ≤ N)
    · simpa only [Int.cast_natCast] using hnear
  have hm := complex_partition_approximation_mean_error E A
    (fun j x => D.frozenCyclicOrbitValue Φ ε b γ (y j) x)
    (fun x : ZMod N => Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)))
    (mul_nonneg (Real.exp_pos _).le hρ.le) hA hsum (fun _ _ => hΦ _) (fun _ => hΦ _) hpoint
  apply hm.trans
  have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  rw [ZMod.card]
  calc
    _ = Real.exp ((p + C) ^ C) * ρ + 2 * ((E.card : ℝ) / N) := by ring
    _ ≤ Real.exp ((p + C) ^ C) * ρ + 2 * (6 * ρ + 3 / N) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeReplacedRankFamily
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def replacedRankResidual (h : ZMod N)
    (c : Fin W.family.outputDim → ZMod N → ℂ)
    (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (W.mixed.evalCyclic N ij.1 (correlationInput h x)) *
    star (c ij.2 x)

theorem exists_rank_approximation_correlation {J : Type*} [Fintype J]
    (hf : ∀ x, ‖f x‖ ≤ 1) (h : W.shifts) (A : J → ZMod N → ℝ)
    (c : J → Fin W.family.outputDim → ZMod N → ℂ) {q : ℝ}
    (hq : 2 ≤ q) (hcard : (Fintype.card J : ℝ) ≤ Real.exp q)
    (hA : ∀ j, PositiveCyclicNiltest.{0} (s - 1) N q (A j))
    (herr : (𝔼 x, ‖W.selectedRank h x -
      ∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x‖) ≤ Real.exp (-(2 * p)) / 2) :
    ∃ j, Nonempty (NativeVectorCorrelation (s - 1) N
      (productNiltestBudget (raisedNiltestBudget (p + q + 2))) (W.replacedRankResidual h.val (c j))) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let b (x : ZMod N) := W.selectedMixed h x * W.selectedLower h x
  have hb (x : ZMod N) : ‖b x‖ ≤ Real.exp p := by
    have hm := W.mixed.norm_eval (W.selectedWitness h).coordinate.1
      (fun i => (((correlationInput h.val x) i).val : ℤ))
    have hl := (W.selectedWitness h).test.eval_budget (W.selectedWitness h).complexity
      (fun _ : Unit => (x.val : ℤ))
    exact (norm_mul _ _).trans_le ((mul_le_mul hm hl (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  let v (j : J) (x : ZMod N) := (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x * b x
  have hmean : (𝔼 x, ‖W.selectedProduct h x - ∑ j, v j x‖) ≤ Real.exp (-p) / 2 := by
    have he := mean_error_mul_bounded (W.selectedRank h)
      (fun x => ∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x) b
      (Real.exp_pos p).le hb herr
    have hid (x : ZMod N) : W.selectedProduct h x - ∑ j, v j x =
        W.selectedRank h x * b x -
        (∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x) * b x := by
      rw [Finset.sum_mul]
      simp only [v, b, W.selectedProduct_eq]
      ring
    have hexp : Real.exp p * (Real.exp (-(2 * p)) / 2) = Real.exp (-p) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    simpa only [hid, hexp] using he
  obtain ⟨j, hj⟩ := exists_correlating_summand_of_mean (multiplicativeDerivative f h.val)
    (W.selectedProduct h) v (Real.exp_pos (-p)) (Real.exp_pos q) hcard
    (multiplicativeDerivative_norm_le_one f hf h.val) hmean (W.selectedProduct_correlation h)
  have hthreshold : Real.exp (-(p + q + 2)) ≤ Real.exp (-p) / (2 * Real.exp q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : Real.exp (-(p + q + 2)) * (2 * Real.exp q) = 2 * Real.exp (-p - 2) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ Real.exp 2 * Real.exp (-p - 2) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
  have hpR : p ≤ p + q + 2 := by linarith
  have hqR : q ≤ p + q + 2 := by linarith
  let V : NativeVectorCorrelation (s - 1) N (p + q + 2)
      (fun ij x => (A j x : ℂ) * W.replacedRankResidual h.val (c j) ij x) := {
    L := (W.selectedWitness h).L
    dim := (W.selectedWitness h).dim
    model := (W.selectedWitness h).model
    test := (W.selectedWitness h).test
    complexity := (W.selectedWitness h).complexity.mono hpR
    coordinate := (W.selectedWitness h).coordinate
    correlation := by
      have hc := hthreshold.trans hj
      have heq (x : ZMod N) : multiplicativeDerivative f h.val x * star (v j x) =
          ((A j x : ℂ) * W.replacedRankResidual h.val (c j) (W.selectedWitness h).coordinate x) *
            star ((W.selectedWitness h).test.evalCyclic N (fun _ => x)) := by
        simp only [v, b, selectedMixed, selectedLower, replacedRankResidual, star_mul,
          Complex.star_def, Complex.conj_ofReal]
        ring
      simpa only [heq] using hc }
  exact ⟨j, V.exists_absorb_positive (W.replacedRankResidual h.val (c j)) (A j)
    (by linarith) ((hA j).mono le_rfl hqR)⟩

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_native_frozen_rank_correlation (s a : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (h : W.shifts) (P : ℝ), 2 ≤ P → p ≤ P →
      ∀ M : ℕ, 0 < M → (M : ℝ) ≤ Real.exp P →
      ∀ ε ξ v γ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ε * ξ * v * γ = W.family.orbit h.val →
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 2) ^ a)) ε.log →
      (∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) x γ) : W.family.model.Space) =
        QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) y γ)) →
      Real.exp ((P + C) ^ C) ≤ N →
      ∃ y : ZMod N,
        (∀ x, ∑ i, ‖W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) ε (ξ * v) γ y x‖ ^ 2 = 1) ∧
        Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
          (W.replacedRankResidual h.val (fun i x => W.family.model.frozenCyclicOrbitValue
            (W.family.vertical.observable i) ε (ξ * v) γ y x))) := by
  obtain ⟨c, _, hfreeze⟩ := exists_partition_orbit_freezing s a
  obtain ⟨b, _, hpart⟩ := exists_interval_residue_partition 1
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_correlation_budget c b
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf h P hP hpP M hM hMP ε ξ v γ hprod hε hperiod hN
  classical
  let : NeZero M := ⟨hM.ne'⟩
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  have hP0 : 0 ≤ P := by linarith
  let D := (P + c) ^ c
  let L := D + 2 * P + 40
  let Q := P + (L + b) ^ b + 2
  let ρ := Real.exp (-L)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hPL : P ≤ L := by dsimp only [L]; linarith
  have hρ : 0 < ρ := Real.exp_pos _
  obtain ⟨hLC, hQC⟩ := hbudget P hP0
  have hlarge : Real.exp L ≤ N := (Real.exp_le_exp.mpr hLC).trans hN
  have hprec : 1 / ρ ≤ Real.exp ((L + 2) ^ 1) := by
    rw [pow_one]
    have he : 1 / ρ = Real.exp L := by simp only [ρ, Real.exp_neg, one_div, inv_inv]
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨n, hn, hcard, A, hA, hsum, hcells⟩ := hpart N M hL
    (hMP.trans (Real.exp_le_exp.mpr hPL)) hρ hprec
  have hqQ : (L + b) ^ b ≤ Q := by dsimp only [Q]; linarith
  have hQ : 2 ≤ Q := by
    have ht : 0 ≤ (L + b) ^ b := by positivity
    dsimp only [Q]
    linarith
  have hDgeom := W.family.complexity.1.mono W.family.model hpP
  have hprod' : ε * (ξ * v) * γ = W.family.orbit h.val := by
    simpa only [mul_assoc] using hprod
  obtain ⟨y, _, hmean⟩ := hfreeze W.family.model (by linarith : 1 ≤ P) hDgeom hρ A
    (fun j x => ((hA j).unit_interval x).1) hsum hcells
    (W.family.vertical.observable (W.selectedWitness h).coordinate.2) W.family.vertical.lipBound
    (W.family.vertical.norm _) (W.family.vertical.lipschitz _)
    (W.family.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP))
    ε (ξ * v) γ (W.family.orbit h.val) hprod' hε hperiod
  let B (j : Fin n × ZMod M) (i : Fin W.family.outputDim) (x : ZMod N) :=
    W.family.model.frozenCyclicOrbitValue (W.family.vertical.observable i) ε (ξ * v) γ (y j) x
  have herror : (𝔼 x, ‖W.selectedRank h x -
      ∑ j, (A j x : ℂ) * B j (W.selectedWitness h).coordinate.2 x‖) ≤ Real.exp (-(2 * p)) / 2 := by
    apply hmean.trans
    exact (frozen_correlation_precision_error P D hD (NeZero.pos N) hlarge).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  obtain ⟨j, V⟩ := W.exists_rank_approximation_correlation hf h A B hQ
    (hcard.trans (Real.exp_le_exp.mpr hqQ))
    (fun j => (hA j).mono (by omega) hqQ) herror
  have hcost : productNiltestBudget (raisedNiltestBudget (p + Q + 2)) ≤ (P + C) ^ C :=
    (frozen_witness_budget_mono (by positivity) (by linarith)).trans hQC
  refine ⟨y j, fun x => W.family.vertical.unit _, ?_⟩
  exact ⟨(Classical.choice V).mono hcost⟩

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)
  {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (E : RationalFilteredNilmanifold L s d) (T : E.DegreeRankStructure r)
  (hpq : p ≤ q) (hT : T.ComplexityLE q)
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

noncomputable def replacementFamily : NativeDegreeRankFamily s r (ZMod N) q where
  L := L
  dim := d
  model := E
  rank := T
  complexity := hT
  orbit := g
  normalized := hg
  outputDim := W.family.outputDim
  output_pos := W.family.output_pos
  output_bound := W.family.output_bound.trans (Real.exp_le_exp.mpr hpq)
  vertical := V

noncomputable def replaceRank (H : Finset (ZMod N)) (hne : H.Nonempty)
    (hdense : Real.exp (-q) * Fintype.card (ZMod N) ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h))))))) :
    NativeCorrelationStructure s r N q f where
  shifts := H
  nonempty := hne
  density := hdense
  mixed := W.mixed.mono hpq
  family := W.replacementFamily E T hpq hT V g hg
  correlation := hcorr

end Erdos3.NativeCorrelationStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)

theorem lipschitz_native_frozenCosetMap {A C : ℝ≥0}
    (hφ : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha : letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith (A * C) (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  exact lipschitz_frozenCosetMap D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ a r h hφ ha

include h in
theorem exists_positive_frozen_observable {A C ℓ : ℝ≥0}
    (hφ : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha : letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x))
    (u : E.Space → ℂ) (hu : letI := E.metricSpace; LipschitzWith ℓ u)
    (hunit : ∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) :
    ∃ v : D.Space → ℂ,
      (letI := D.metricSpace; LipschitzWith (ℓ * (A * C)) v) ∧
      (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
      ∀ x : D.RealGroup, v (QuotientGroup.mk x) = u (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  let := D.metricSpace
  let := E.metricSpace
  let f := frozenCosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h
  have hf : LipschitzWith (A * C) f := D.lipschitz_native_frozenCosetMap E φ a r h hφ ha
  refine ⟨u ∘ f, hu.comp hf, fun x => hunit (f x), ?_, fun _ => rfl⟩
  intro x
  change ‖u (f x)‖ ≤ 1
  rw [← positiveClip_eq_self (u (f x)) (hunit (f x))]
  exact norm_positiveClip_le_one _

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

open Module NilpotentLieBCHGroup

noncomputable def conjugationPullback {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) : Subgroup D.filtration.Group :=
  ⨅ z : {z : E.filtration.Group // E.basis.equivFun z.coord ∈ denominatorGrid q},
    (E.lattice.map (MulAut.conj z.val).toMonoidHom).comap
      (NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ)

theorem exists_uniform_conjugated_source_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.conjugationPullback E φ q ∧ Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hconj⟩ := exists_uniform_conjugated_inner_grid s
  let X : Polynomial ℕ := Polynomial.X
  let U := X + 1 + (X + 1 + Polynomial.C a) ^ a + (X + 2) ^ 3
  let P := U + 2 * U ^ 2 + (U + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  classical
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  obtain ⟨B, hB, hBb, hBgrid⟩ := hconj E.basis E.filtration.lowerCentralSeries_eq_bot
    E.lattice E.grid q H t E.grid_pos hq E.inner_grid ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (hE.2.1.trans (Real.exp_le_exp.mpr hpt)) (hqp.trans (Real.exp_le_exp.mpr hpt))
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := B * matrixDenominator A
  have hN₀ : 0 < N₀ := Nat.mul_pos hB (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis (D.conjugationPullback E φ q) := by
    intro x hx
    change (⟨D.basis.equivFun.symm x⟩ : D.filtration.Group) ∈ D.conjugationPullback E φ q
    apply Subgroup.mem_iInf.mpr
    intro z
    change x ∈ bchSubgroupCoordinates D.basis
      ((E.lattice.map (MulAut.conj z.val).toMonoidHom).comap
        (NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    rw [bchSubgroupCoordinates_comap D.basis E.basis φ]
    exact hBgrid z.val z.property (matrix_mulVec_fine_grid A B hx)
  let u := t + (t + a) ^ a + (p + 2) ^ 3
  have htu : t ≤ u := by
    exact (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg a)) _)).trans
      (le_add_of_nonneg_right (pow_nonneg (by linarith) _))
  have hu : 0 ≤ u := ht.trans htu
  have hpu : p ≤ u := hpt.trans htu
  have hN₀b : (N₀ : ℝ) ≤ Real.exp u := by
    calc
      _ = (B : ℝ) * matrixDenominator A := Nat.cast_mul _ _
      _ ≤ Real.exp ((t + a) ^ a) * Real.exp ((p + 2) ^ 3) :=
        mul_le_mul hBb hAb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((t + a) ^ a + (p + 2) ^ 3) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [u]; linarith)
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice (D.conjugationPullback E φ q)
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hu
      (by simpa only [Fintype.card_fin] using hD.1.trans hpu)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpu)) hN₀b
  have hsum : u + 2 * u ^ 2 + (u + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, U, X, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_right (by positivity : 0 ≤ 2 * u ^ 2)).trans
      (le_add_of_nonneg_right (sq_nonneg (u + 2)))).trans hsum
  have hiC : 2 * u ^ 2 ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_left hu).trans (le_add_of_nonneg_right (sq_nonneg (u + 2)))).trans hsum
  have hgC : (u + 2) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (add_nonneg hu (by positivity))).trans hsum
  exact ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hiC), N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpu.trans huC) (hNb.trans (Real.exp_le_exp.mpr hgC))⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem real_conjugationPullback_property {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hΛ : Λ ≤ D.conjugationPullback E φ q)
    (r : E.RealGroup) (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    ∀ γ ∈ Λ.map realificationHom,
      r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice := by
  obtain ⟨z, hz, rfl⟩ := (realification_grid_iff
    (hnil := E.filtration.lowerCentralSeries_eq_bot) E.basis q hq r).mp hr
  intro γ hγ
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hγ
  have h := Subgroup.mem_iInf.mp (hΛ hc) ⟨z, hz⟩
  change NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ c ∈
      E.lattice.map (MulAut.conj z).toMonoidHom at h
  obtain ⟨v, hv, heq⟩ := Subgroup.mem_map.mp h
  have hconj : z⁻¹ * NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ c * z = v := by
    rw [← heq]
    change z⁻¹ * (z * v * z⁻¹) * z = v
    group
  rw [realificationMap_realificationHom, ← map_inv, ← map_mul, ← map_mul, hconj]
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_coset_map (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∃ (f : Q.Space → E.Space) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (letI := Q.metricSpace; letI := E.metricSpace; LipschitzWith K f) ∧
              ∀ x : Q.RealGroup, f (QuotientGroup.mk x) = QuotientGroup.mk
                (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  let f := frozenCosetMap Q.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r hconj
  have hf : letI := Q.metricSpace; letI := E.metricSpace; LipschitzWith (A * B) f :=
    Q.lipschitz_native_frozenCosetMap E φ a r hconj hBLip ha'
  refine ⟨f, A * B, ?_, hf, fun _ => rfl⟩
  calc
    _ = (A : ℝ) * B := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) :=
      mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le
    _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_map (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∃ h : ∀ γ ∈ Q.realLattice,
                r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice,
              ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q.metricSpace
                 letI := E.metricSpace
                 LipschitzWith K (frozenCosetMap Q.realLattice E.realLattice
                   (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                     (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h)) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  refine ⟨hconj, A * B, ?_, Q.lipschitz_native_frozenCosetMap E φ a r hconj hBLip ha'⟩
  calc
    _ = (A : ℝ) * B := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) :=
      mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le
    _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem realificationMap_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (x : D.RealGroup) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x.coord = x.coord
  generalize x.coord = y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem exists_uniform_unit_frozen_cover (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (p : ℝ), 0 ≤ p → R.ComplexityLE p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (R.withLattice Λ N hN hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p) (a u : D.RealGroup),
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun u.coord ∈ realDenominatorGrid q →
            ∃ U : (D.withLattice Λ N hN hin hout).UnitVerticalObservable
                ((R.withLattice Λ N hN hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ ∀ i x,
                U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk (a * x * u)) := by
  obtain ⟨b, _, hcover⟩ := exists_uniform_frozen_coset_map s k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d r D R p hp hR q hq hqp
  classical
  have hcost : p + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hbp : 0 ≤ (p + b) ^ b := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hbC : (p + b) ^ b ≤ (p + C) ^ C := by linarith
  have hidheight (i j : Fin d) : rationalLogHeight (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) (D.basis j)) i) ≤ p := by
    change rationalLogHeight (D.basis.repr (D.basis j) i) ≤ p
    by_cases hji : j = i
    · subst i
      simpa [rationalLogHeight] using hp
    · simpa [Basis.repr_self, Finsupp.single_apply, hji, rationalLogHeight] using hp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmaps⟩ :=
    hcover D D (LieHom.id : L →ₗ⁅ℚ⁆ L) p hp hR.1 hR.1 hidheight q hq hqp
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hbC),
    N, hN, hin, hout, R.withLattice_complexity Λ N hN hin hout hR hpC
      (hQ.mono _ hbC), ?_⟩
  intro V a u ha hu
  obtain ⟨f, K, hK, hLip, hf⟩ := hmaps a u ha hu
  have hfid (x : D.RealGroup) : f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * u) := by
    simpa only [D.realificationMap_id_apply] using hf x
  have hVK : ((V.lipBound * K : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (V.lipBound : ℝ) * K := NNReal.coe_mul _ _
      _ ≤ Real.exp p * Real.exp ((p + b) ^ b) :=
        mul_le_mul V.lip_bound hK K.coe_nonneg (Real.exp_pos p).le
      _ = Real.exp (p + (p + b) ^ b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  let U := V.frozenCover R Λ hΛ N hN hin hout a u f hfid K hLip hpC hVK
  refine ⟨U, rfl, ?_⟩
  intro i x
  exact congrArg (V.observable i) (hfid x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_shared_frozen_unit_observable (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r) {p ε : ℝ},
      0 ≤ p → R.ComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
        (H : Finset G) (a u : G → D.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, (D.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m),
          (R.withLattice Λ m hm hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (D.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((R.withLattice Λ m hm hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧
              ∀ h ∈ H', ∀ i x, ‖V.observable i (QuotientGroup.mk (a h * x * u h)) -
                U.observable i (QuotientGroup.mk x)‖ ≤ (V.lipBound : ℝ) * ε := by
  obtain ⟨b, _, hselect⟩ := exists_native_frozen_parameter_fiber s k
  obtain ⟨c, _, hcover⟩ := exists_uniform_unit_frozen_cover s k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C b) ^ b + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro G L I _ _ _ _ _ _ _ d r D R p ε hp hR hε hεp q hq hqp V H a u hH ha hu hugrid
  have hsum : (p + b) ^ b + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hb : (p + b) ^ b ≤ (p + C) ^ C := by
    have : 0 ≤ (p + c) ^ c := by positivity
    linarith
  have hc : (p + c) ^ c ≤ (p + C) ^ C := by
    have : 0 ≤ (p + b) ^ b := by positivity
    linarith
  obtain ⟨H', hsub, hnonempty, hdense, a₀, u₀, ha₀, _, hu₀, hclose⟩ :=
    hselect D hp hR.1 hε hεp q hq hqp H a u hH ha hu hugrid
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hRank, hU⟩ :=
    hcover (I := I) D R p hp hR q hq hqp
  obtain ⟨U, hfreq, hval⟩ := hU V a₀ u₀ ha₀ hu₀
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    m, hm, hin, hout, hRank.mono _ hc, H', hsub, hnonempty, ?_, U.mono hc, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hb))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh i x
    let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    obtain ⟨hdist, hu⟩ := hclose h hh
    change ‖V.observable i (QuotientGroup.mk (a h * x * u h)) -
      U.observable i (QuotientGroup.mk x)‖ ≤ _
    rw [hval, hu]
    exact (D.frozen_observable_change_left (V.observable i) (V.lipschitz i) (a h) a₀ x u₀).trans
      (mul_le_mul_of_nonneg_left hdist V.lipBound.coe_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem NativeCorrelationStructure.replacedRankResidual_norm_sub_le
    {s r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p F) (hF : ∀ x, ‖F x‖ ≤ 1)
    (h : ZMod N) (c c' : Fin W.family.outputDim → ZMod N → ℂ)
    (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) (x : ZMod N) :
    ‖W.replacedRankResidual h c ij x - W.replacedRankResidual h c' ij x‖ ≤
      ‖c ij.2 x - c' ij.2 x‖ := by
  unfold NativeCorrelationStructure.replacedRankResidual
  rw [← mul_sub, ← star_sub, norm_mul, norm_mul, norm_star, norm_star]
  have hd := multiplicativeDerivative_norm_le_one F hF h x
  have hm := W.mixed.norm_eval ij.1 (fun j => (((correlationInput h x) j).val : ℤ))
  have hmul : ‖multiplicativeDerivative F h x‖ *
      ‖W.mixed.evalCyclic N ij.1 (correlationInput h x)‖ ≤ 1 := by
    exact (mul_le_mul hd hm (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hmul

theorem exists_native_shared_frozen_correlations (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      0 ≤ P → p ≤ P → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp P →
      ∀ (H : Finset (ZMod N)) (a u : ZMod N → W.family.model.RealGroup)
        (b : ZMod N → ZMod N → W.family.model.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(W.family.model.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((P + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(W.family.model.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((P + 2) ^ k)) →
      (∀ h ∈ H, (W.family.model.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N P
        (W.replacedRankResidual h (fun i x => W.family.vertical.observable i
          (QuotientGroup.mk (a h * b h x * u h)))))) →
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
                (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk (b h x))))) := by
  obtain ⟨a₀, _, hshared⟩ := exists_shared_frozen_unit_observable s k
  let Q : Polynomial ℕ := 3 * Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C a₀) ^ a₀ + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P F W hF hP hpP q hq hqP H a u b hH ha hu hugrid hcorr
  let T := 3 * P + 2
  let ε := Real.exp (-T)
  have hPT : P ≤ T := by dsimp only [T]; linarith
  have hpT : p ≤ T := hpP.trans hPT
  have hT : 0 ≤ T := hP.trans hPT
  have hε : 0 < ε := Real.exp_pos _
  have hεT : 1 / ε ≤ Real.exp T := by simp only [ε, one_div, ← Real.exp_neg, neg_neg, le_refl]
  have hsum : T + (T + a₀) ^ a₀ + 2 ≤ (P + C) ^ C := by
    simpa [Q, T, Polynomial.eval₂_pow] using hbudget P hP
  have hTC : (T + a₀) ^ a₀ ≤ (P + C) ^ C := by linarith
  have hPC : P + 1 ≤ (P + C) ^ C := by
    have : 0 ≤ (T + a₀) ^ a₀ := by positivity
    linarith
  have hbound : Real.exp ((P + 2) ^ k) ≤ Real.exp ((T + 2) ^ k) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, happ⟩ :=
    hshared W.family.model W.family.rank hT (W.family.complexity.mono _ hpT)
      hε hεT q hq (hqP.trans (Real.exp_le_exp.mpr hPT))
      (W.family.vertical.mono hpT) H a u hH
      (fun h hh i => (ha h hh i).trans hbound)
      (fun h hh i => (hu h hh i).trans hbound) hugrid
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hTC),
    m, hm, hin, hout, hRank.mono _ hTC, H', hsub, hnonempty, ?_, U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hTC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    have hprecision : (W.family.vertical.lipBound : ℝ) * ε ≤ Real.exp (-(2 * P)) / 2 := by
      calc
        _ ≤ Real.exp P * ε := mul_le_mul_of_nonneg_right
          (W.family.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP)) hε.le
        _ = Real.exp (-(2 * P) - 2) := by
          dsimp only [ε, T]
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(2 * P) - 1) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ _ := exp_sub_one_le_half_exp _
    obtain ⟨V⟩ := hcorr h (hsub hh)
    obtain ⟨V'⟩ := V.exists_of_uniform_approx
      (W.replacedRankResidual h (fun i x => (U.mono hTC).observable i (QuotientGroup.mk (b h x))))
      (fun ij x => (W.replacedRankResidual_norm_sub_le hF h _ _ ij x).trans
        ((happ h hh ij.2 (b h x)).trans hprecision))
    exact ⟨V'.mono hPC⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def topQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ F.layerIdeal (s + 1)) s
      (Fintype.card {i : Fin d // ¬ s + 1 ≤ w i}) :=
  F.coordinateQuotientModel b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout

theorem topQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p)
    (hgeom : (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  apply F.coordinateQuotientModel_geometry b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout hp
  · simpa only [Fintype.card_fin] using hgeom.1
  · exact hgeom.2.1
  · exact hgeom.2.2.1

@[simp] theorem topQuotientModel_filtration (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).filtration = F.quotientTop := rfl

@[simp] theorem topQuotientModel_lattice (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).lattice =
      Γ.map (F.quotientStepHom (F.layerIdeal (s + 1)) le_rfl) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem quotientFinBasis_repr_mk {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (x : L) (k : Fin (Fintype.card {i // i ∉ S})) :
    (quotientFinBasis b I S hspan).repr (lieQuotientMap I x) k =
      b.repr x ((Fintype.equivFin {i // i ∉ S}).symm k) := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hspan x _

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_quotient {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
        Q.filtration = D.filtration.quotientTop ∧
        Q.lattice = D.lattice.map
          (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
        Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
        (∀ i k, rationalLogHeight (Q.basis.repr
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis i)) k) ≤ (p + 3) ^ 5) ∧
        ∃ w : Fin n → ℕ, ∀ j, Q.filtration.layer j = Submodule.span ℚ (Q.basis '' {i | j ≤ w i}) := by
  classical
  obtain ⟨b, w, N, _, _, hF, _, hinverse, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let Q := D.filtration.topQuotientModel b w hF D.lattice N hN hin hout
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hn : Fintype.card {i : Fin (finrank ℚ L) // ¬ s + 1 ≤ w i} ≤ d := by
    simpa only [Fintype.card_fin, hdim] using
      Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => ¬ s + 1 ≤ w i)
  have hp1 : 0 ≤ p + 1 := by linarith
  have hpPow : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget hp1 (by decide : 1 ≤ 11))
  have hpr : p ≤ (p + 3) ^ 11 := (by linarith : p ≤ p + 1).trans hpPow
  have hbase : 1 ≤ p + 3 := by linarith
  have h9 : (p + 3) ^ 9 ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hbase (by decide)
  have hgeom : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.topQuotientModel_geometry b w hF D.lattice N hN hin hout (by positivity)
    apply D.filtration.ofAdaptedBasis_geometry b w hF D.lattice N hN hin hout (by positivity)
    · exact (by simpa only [hdim] using hD.1 : (finrank ℚ L : ℝ) ≤ p).trans hpr
    · exact hNp.trans (Real.exp_le_exp.mpr h9)
    · exact hbracket
  refine ⟨_, hn, Q, rfl, rfl, hgeom, ?_, quotientFinWeight w {i | s + 1 ≤ w i}, ?_⟩
  · intro i k
    have hspan : (D.filtration.layerIdeal (s + 1)).toSubmodule =
        Submodule.span ℚ (b '' {i | s + 1 ≤ w i}) := hF (s + 1)
    have hcoord := quotientFinBasis_repr_mk b (D.filtration.layerIdeal (s + 1))
      {i | s + 1 ≤ w i} hspan (D.basis i) k
    exact (congrArg rationalLogHeight hcoord).le.trans (hinverse i _)
  · intro j
    exact D.filtration.quotientFinBasis_layers b w hF (D.filtration.layerIdeal (s + 1)) le_rfl
      {i | s + 1 ≤ w i} (hF (s + 1)) j

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

theorem exists_controlled_reduced_square_geometry {p : ℝ}
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom⟩ :=
    D.exists_controlled_square_geometry hp hD
  exact ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom,
    D.filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _
      (squareGeometryBudget_nonneg hp) hgeom⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_subspace_quotient
    {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (vK : κ → K) (hspanK : Submodule.span ℚ (Set.range vK) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hvK : ∀ j i, rationalLogHeight (D.basis.repr (vK j : L) i) ≤ p) :
    let I := D.filtration.topSubspaceIdeal K hK
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
      Q.filtration = D.filtration.quotientLie I hI ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
      Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 3) ^ 5 := by
  classical
  intro I hI
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  obtain ⟨b, w, S, hw, hcentral, hb, hlayers, hKS⟩ :=
    D.filtration.exists_bounded_adapted_basis_with_top_subspace hs D.basis
      (fun i => D.layerBasis i) (fun i => (D.layerBasis i).span_eq) K hK vK hspanK
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.2 i j k))
      (fun j i => rationalHeightLE_ceil_exp (hvK j i))
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by simpa only [hdim] using hd
  obtain ⟨N, hN, hNp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hb D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 1) hd hr hHp
    (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbinv := inverse_basis_entries_height D.basis b hH hb
  have hc := basis_change_structure_height D.basis b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hcb := rationalLieStructureHeight_inverse_budget (Fintype.card (Fin d))
    (Fintype.card (Fin (finrank ℚ L))) H (by linarith : 0 ≤ p + 1) hd hr hHp
  have hsolve := rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H
    (by linarith : 0 ≤ p + 1) hr hHp
  have hspanI : I.toSubmodule = Submodule.span ℚ (b '' S) := hKS
  let Q := D.filtration.coordinateQuotientModel b w hlayers I hI S hspanI D.lattice N hN hin hout
  have hbig : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      le_power_budget (by linarith : 0 ≤ p + 1) (by decide : 1 ≤ 11)
  have hgeometry : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.coordinateQuotientModel_geometry b w hlayers I hI S hspanI
      D.lattice N hN hin hout (by positivity) (hr.trans hbig)
    · apply hNp.trans (Real.exp_le_exp.mpr ?_)
      rw [show p + 1 + 2 = p + 3 by ring]
      exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 9 ≤ 11)
    · intro i j k
      apply rationalLogHeight_le_of_height (hc i j k)
      simpa only [show p + 1 + 2 = p + 3 by ring] using hcb
  refine ⟨_, ?_, Q, rfl, rfl, hgeometry, ?_⟩
  · simpa only [Fintype.card_fin, hdim] using Fintype.card_subtype_le (fun i => i ∉ S)
  · intro i j
    have hcoord := quotientFinBasis_repr_mk b I S hspanI (D.basis i) j
    change rationalLogHeight ((quotientFinBasis b I S hspanI).repr (lieQuotientMap I (D.basis i)) j) ≤ _
    rw [hcoord]
    apply rationalLogHeight_le_of_height (hbinv i _)
    simpa only [show p + 1 + 2 = p + 3 by ring] using hsolve

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

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

theorem exists_uniform_frozen_descent (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      {w : σ → ℕ} (T : E.Niltest w)
      (g : D.filtration.realification.PolynomialOrbit w) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ d ∧
          ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
            ∃ hQF : Q.filtration = D.filtration.quotientTop,
              Q.lattice = Λ.map
                (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∀ a r : E.RealGroup,
                 (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
                 (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
                 (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
                 ∃ S : Q.Niltest w, S.orbit = D.topQuotientOrbit Q hQF g ∧
                   S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
                   ∀ x : σ → ℤ, S.eval x = T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ
                       (D.filtration.realification.polynomialOrbitEval w x g) * r))) := by
  obtain ⟨A, _, hmaps⟩ := exists_uniform_frozen_map (s + 1) k
  obtain ⟨B, _, hdesc⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := X + U + 4
  let R := P + (P + 3) ^ 11 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w T g p hp hD hT hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hF, hmap⟩ :=
    hmaps D E φ p hp hD hT.1 hφ q hq hqp
  let F := D.withLattice Λ N hN hin hout
  let u := (p + A) ^ A
  let t := p + u + 4
  let r := t + (t + 3) ^ 11 + 4
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hut : u ≤ t := by dsimp [t]; linarith
  have htr : t ≤ r := by dsimp [r]; linarith [pow_nonneg (by linarith : 0 ≤ t + 3) 11]
  have hr : 0 ≤ r := ht.trans htr
  have hQr : (t + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hsum : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, P, U, X, r, t, u, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ :=
    F.exists_controlled_top_quotient ht (hF.mono F hut)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr ((hut.trans htr).trans hrC)),
    n, hn, Q, hQF, hQL, hQ.mono Q (hQr.trans hrC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  intro a b ha hb hinvariant
  obtain ⟨hconj, K, hK, hKlip⟩ := hmap a b ha hb
  let T' := F.frozenComplexNiltest E φ a b hconj T g K hKlip
  have hT' : T'.ComplexityLE t :=
    F.frozenComplexNiltest_complexity E φ a b hconj T g K hKlip hp hu hF hT hK
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  obtain ⟨S, hSo, hSn, hSc, hSe⟩ := hdesc F Q hQF hQL T' r hr (hT'.mono htr)
    (hQ.mono Q hQr) (fun i j => (hproj j i).trans (h5.trans hQr))
    (F.frozenComplexNiltest_top_invariant E φ a b hconj T g K hKlip hinvariant)
  refine ⟨S, hSo, hSn, hSc.mono hcost, ?_⟩
  intro x
  exact (hSe x).trans (F.frozenComplexNiltest_eval E φ a b hconj T g K hKlip x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

noncomputable def basisOfTail (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) : Basis (Fin (finrank ℚ P)) ℚ P := by
  classical
  let a := supportedSubmoduleBasis b P {j | c ≤ j.val} (hP.trans (basisTail_eq_span b c))
  exact a.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis a).symm)

theorem basisOfTail_height (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) (i : Fin (finrank ℚ P)) (j : Fin d) :
    RationalHeightLE (b.repr (basisOfTail b P c hP i : L) j) 1 := by
  classical
  unfold basisOfTail
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one b _ j

theorem tail_span_basis_members (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) : P = Submodule.span ℚ (b '' {j | b j ∈ P}) := by
  apply le_antisymm
  · conv_lhs => rw [hP, basisTail_eq_span]
    apply Submodule.span_mono
    rintro x ⟨j, hj, rfl⟩
    exact ⟨j, hP.symm ▸ basis_mem_tail b j hj, rfl⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨j, hj, rfl⟩; exact hj)

theorem NilpotentLieFiltration.exists_weights_of_tails {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L)
    (htail : ∀ i, ∃ c, F.layer i = basisTail b c) :
    ∃ w : Fin d → ℕ, ∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j}) := by
  let S : Fin (s + 1) → Set (Fin d) := fun i => {j | b j ∈ F.layer (i.val + 1)}
  have hS : Antitone S := fun _ _ h _ hx => F.antitone (Nat.add_le_add_right h 1) hx
  let w := nestedSupportWeight S
  refine ⟨w, F.layer_eq_span_of_weighted_flag b w (fun j => nestedSupportWeight_le S j) ?_⟩
  intro i
  obtain ⟨c, hc⟩ := htail (i.val + 1)
  rw [tail_span_basis_members b _ c hc]
  apply congrArg (Submodule.span ℚ)
  apply congrArg (fun A : Set (Fin d) => b '' A)
  ext j
  exact mem_nestedSupport_iff S hS i j

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration

theorem exists_coordinate_quotient_layer_basis
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (P : Submodule ℚ L) (T : Set ι) (hP : P = Submodule.span ℚ (b '' T)) :
    ∃ a : Basis (Fin (finrank ℚ (P.map (lieQuotientMap I).toLinearMap))) ℚ
        (P.map (lieQuotientMap I).toLinearMap),
      ∀ i j, rationalLogHeight ((quotientFinBasis b I S hI).repr (a i : L ⧸ I) j) ≤ 0 := by
  classical
  let q := supportedQuotientBasis b I.toSubmodule S hI
  have hspan : P.map (lieQuotientMap I).toLinearMap =
      Submodule.span ℚ (q '' {i : {i // i ∉ S} | i.val ∈ T}) := by
    rw [hP]
    exact supportedQuotientBasis_map_span b I.toSubmodule S hI T
  let a := supportedSubmoduleBasis q (P.map (lieQuotientMap I).toLinearMap)
    {i : {i // i ∉ S} | i.val ∈ T} hspan
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis a).symm
  refine ⟨a.reindex e, ?_⟩
  intro i j
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe,
    quotientFinBasis, Basis.repr_reindex_apply]
  change rationalLogHeight (q.repr (q (e.symm i).val)
    ((Fintype.equivFin {i // i ∉ S}).symm j)) ≤ 0
  rw [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> norm_num [rationalLogHeight]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedSquareBasis_projection_height (e : Basis ι ℚ L) (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (i : κ ⊕ {i // 2 ≤ w i}) (k : ι) :
    RationalHeightLE (e.repr (F.squareFst (F.adaptedSquareBasis b w h i)) k) H ∧
      RationalHeightLE (e.repr (F.squareSnd (F.adaptedSquareBasis b w h i)) k) H := by
  cases i with
  | inl i =>
    simpa only [squareFst_apply, squareSnd_apply, adaptedSquareBasis_inl] using
      And.intro (hb k i) (hb k i)
  | inr i =>
    constructor
    · simpa only [squareFst_apply, adaptedSquareBasis_inr] using hb k i
    · simp only [squareSnd_apply, adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hH

variable [Fintype κ]

theorem squareFinBasis_projection_height (e : Basis ι ℚ L) (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (i : Fin (Fintype.card (κ ⊕ {i // 2 ≤ w i}))) (k : ι) :
    RationalHeightLE (e.repr (F.squareFst (F.squareFinBasis b w h i)) k) H ∧
      RationalHeightLE (e.repr (F.squareSnd (F.squareFinBasis b w h i)) k) H := by
  simp only [squareFinBasis, Basis.reindex_apply]
  exact F.adaptedSquareBasis_projection_height e b w h hH hb _ k

theorem quotientFinBasis_projection_height (b : Basis κ ℚ L) (I : LieIdeal ℚ L)
    (S : Set κ) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i : κ) (j : Fin (Fintype.card {i // i ∉ S})) :
    RationalHeightLE ((quotientFinBasis b I S hspan).repr (lieQuotientMap I (b i)) j) 1 := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_projection_height b I S hspan i _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem rankFlag_span_height {H : ℕ}
    (hR : ∀ i j a k, RationalHeightLE (D.basis.repr (R.basis i j a : L) k) H)
    (n : Fin ((s + 1) * (s + 1) + 1)) :
    Submodule.span ℚ ({x : L | ∀ k, RationalHeightLE (D.basis.repr x k) H} ∩
      (R.filtration.rankFlag n.val : Set L)) = R.filtration.rankFlag n.val := by
  by_cases hn : n.val < (s + 1) * (s + 1)
  · obtain ⟨hi, hj⟩ := DegreeRankLieFiltration.rankFlag_decode_lt hn
    let i : Fin (s + 1) := ⟨n.val / (s + 1), by omega⟩
    let j : Fin (s + 1) := ⟨n.val % (s + 1), by omega⟩
    exact span_inter_eq_of_spanning_family _ (R.basis i j) (R.basis i j).span_eq _
      (fun a => hR i j a)
  · have heq : n.val = (s + 1) * (s + 1) := by omega
    rw [heq, R.filtration.rankFlag_terminal]
    exact le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) bot_le

theorem exists_bounded_rank_adapted_basis {H : ℕ}
    (hR : ∀ i j a k, RationalHeightLE (D.basis.repr (R.basis i j a : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧ (∀ a k, RationalHeightLE (D.basis.repr (b a) k) H) ∧
      ∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail b c := by
  let := D.basis.finiteDimensional_of_finite
  let N := (s + 1) * (s + 1)
  let S : Set L := {x | ∀ k, RationalHeightLE (D.basis.repr x k) H}
  let P : Fin (N + 1) → Submodule ℚ L := fun n => R.filtration.rankFlag n.val
  have hP : Antitone P := fun _ _ h => R.filtration.rankFlag_antitone h
  have hspan : ∀ n, Submodule.span ℚ (S ∩ (P n : Set L)) = P n := R.rankFlag_span_height hR
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := R.filtration.rankFlag_zero.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hspan 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, _, hb, hflag⟩ := exists_sorted_flag_basis_from_spanning_set P hP S hS hspan
  have hcentral : IsCentralLieBasis b := centralLieBasis_of_finite_flag R.filtration.rankFlag b w
    R.filtration.rankFlag_zero R.filtration.rankFlag_terminal
    (fun _ {_ _} hy => R.filtration.rankFlag_lie_mem hy) hw hflag
  refine ⟨b, hcentral, hb, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := R.filtration.layer_eq_rankFlag i j
  exact ⟨weightCut w k.val, weightCut_le w k.val,
    hk.trans ((hflag k).trans (span_weight_gt_eq_basisTail b w hw k.val))⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem exists_controlled_rank_adapted_basis {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (N : ℕ),
      IsCentralLieBasis b ∧
      (∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail b c) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N := by
  let := D.basis.finiteDimensional_of_finite
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := by linarith
  have hd : (d : ℝ) ≤ p + 1 := hR.1.1.trans (by linarith)
  have hr : (finrank ℚ L : ℝ) ≤ p + 1 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hd
  have hgrid : (D.grid : ℝ) ≤ Real.exp (p + 1) :=
    hR.1.2.1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨b, hcentral, hb, htail⟩ := R.exists_bounded_rank_adapted_basis
    (fun i j a k => rationalHeightLE_ceil_exp (hR.2 i j a k))
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hb D.inner_grid D.outer_grid hp1
    (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hr) hHp hgrid
  have hInv := inverse_basis_entries_height D.basis b hH hb
  have hStructure := basis_change_structure_height D.basis b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hR.1.2.2.1 i j k))
  have hSolveBudget := rationalSolveHeight_le_budget (finrank ℚ L) H hp1 hr hHp
  have hStructureBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ L) H hp1 hd hr hHp
  have hshift : p + 1 + 2 = p + 3 := by ring
  refine ⟨b, N, hcentral, htail, ?_, ?_, ?_, hN, ?_, hin, hout⟩
  · exact fun j i => rationalLogHeight_le_of_height (hb j i) hHp
  · intro i j
    apply rationalLogHeight_le_of_height (hInv i j)
    simpa only [Fintype.card_fin, hshift] using hSolveBudget
  · intro i j k
    apply rationalLogHeight_le_of_height (hStructure i j k)
    simpa only [Fintype.card_fin, hshift] using hStructureBudget
  · simpa only [hshift] using hNb

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

structure AdaptedData (R : D.DegreeRankStructure r) extends D.AdaptedModelData where
  central : IsCentralLieBasis basis
  rank_layers : ∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail basis c

namespace AdaptedData

variable {R : D.DegreeRankStructure r} (F : R.AdaptedData)

noncomputable def model : RationalFilteredNilmanifold L s (finrank ℚ L) := F.toAdaptedModelData.model

noncomputable def rank : F.model.DegreeRankStructure r where
  filtration := R.filtration
  associated := R.associated
  basis i j := basisOfTail F.basis _ (Classical.choose (F.rank_layers i.val j.val))
    (Classical.choose_spec (F.rank_layers i.val j.val)).2

theorem model_geometry_of_bounds {p : ℝ} (hp : 0 ≤ p) (hd : (finrank ℚ L : ℝ) ≤ p)
    (hgrid : (F.grid : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants F.basis i j k) ≤ p) :
    F.model.GeometryComplexityLE p :=
  D.filtration.ofAdaptedBasis_geometry F.basis F.weight F.layers D.lattice F.grid F.grid_pos
    F.inner F.outer hp hd hgrid hc

theorem rank_complexity {p : ℝ} (hp : 0 ≤ p) (hF : F.model.GeometryComplexityLE p) :
    F.rank.ComplexityLE p := by
  refine ⟨hF, ?_⟩
  intro i j a k
  apply rationalLogHeight_le_of_height
    (basisOfTail_height F.basis _ (Classical.choose (F.rank_layers i.val j.val))
      (Classical.choose_spec (F.rank_layers i.val j.val)).2 a k)
  simpa only [Nat.cast_one] using Real.one_le_exp hp

end AdaptedData

theorem exists_rank_adapted_data (R : D.DegreeRankStructure r) {p : ℝ}
    (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ F : R.AdaptedData, F.rank.ComplexityLE ((p + 3) ^ 11) ∧
      (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1) ∧
      ∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + 3) ^ 5 := by
  obtain ⟨b, N, hcentral, htail, hb, hinv, hc, hN, hNb, hin, hout⟩ :=
    R.exists_controlled_rank_adapted_basis hp hR
  have hOrd : ∀ i, ∃ c, D.filtration.layer i = basisTail b c := by
    intro i
    obtain ⟨c, _, h⟩ := htail i 0
    refine ⟨c, ?_⟩
    rw [← R.associated]
    exact h
  obtain ⟨w, hw⟩ := D.filtration.exists_weights_of_tails b hOrd
  let F : R.AdaptedData := {
    basis := b
    weight := w
    layers := hw
    grid := N
    grid_pos := hN
    inner := hin
    outer := hout
    central := hcentral
    rank_layers := htail
  }
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hR.1.1.trans hpow
  have hgeom : F.model.GeometryComplexityLE ((p + 3) ^ 11) :=
    F.model_geometry_of_bounds (by positivity) hdim
      (hNb.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc
  exact ⟨F, F.rank_complexity (by positivity) hgeom, hb, hinv⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
  (F : R.AdaptedData)

theorem exists_lower_rank_quotient {p : ℝ} (hp : 0 ≤ p) (hF : F.model.GeometryComplexityLE p) :
    let I := R.filtration.layerIdeal s (r + 1)
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    ∃ n : ℕ, n ≤ finrank ℚ L ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        ∃ U : Q.DegreeRankStructure r,
          U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
          Q.filtration = D.filtration.quotientLie I hI ∧
          Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
          U.ComplexityLE p ∧
          (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (F.basis i)) j) ≤ 0) ∧
          ∀ j, ∃ k, ∀ x : L, Q.basis.repr (lieQuotientMap I x) j = F.basis.repr x k := by
  intro I hI
  classical
  let S : Set (Fin (finrank ℚ L)) := {i | F.basis i ∈ I}
  have hspan : I.toSubmodule = Submodule.span ℚ (F.basis '' S) := by
    obtain ⟨c, _, hc⟩ := F.rank_layers s (r + 1)
    exact tail_span_basis_members F.basis _ c hc
  let Q := D.filtration.coordinateQuotientModel F.basis F.weight F.layers I hI S hspan
    D.lattice F.grid F.grid_pos F.inner F.outer
  let G := R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree)
  have hG : G.associatedDegree = Q.filtration := by
    apply NilpotentLieFiltration.eq_of_layer_eq
    funext j
    change (R.filtration.layer j 0).map (lieQuotientMap I).toLinearMap =
      (D.filtration.layer j).map (lieQuotientMap I).toLinearMap
    exact congrArg (fun P : Submodule ℚ L => P.map (lieQuotientMap I).toLinearMap)
      (congrArg (fun H : NilpotentLieFiltration L s => H.layer j) R.associated)
  have hbase (i j : Fin (s + 1)) :
      ∃ b : Basis (Fin (finrank ℚ (G.layer i.val j.val))) ℚ (G.layer i.val j.val),
        ∀ a k, rationalLogHeight (Q.basis.repr (b a : L ⧸ I) k) ≤ 0 := by
    obtain ⟨c, _, hc⟩ := F.rank_layers i.val j.val
    exact exists_coordinate_quotient_layer_basis F.basis I S hspan (R.filtration.layer i.val j.val)
      {k | c ≤ k.val} (hc.trans (basisTail_eq_span F.basis c))
  choose b hb using hbase
  let U : Q.DegreeRankStructure r := ⟨G, hG, b⟩
  have hQ : Q.GeometryComplexityLE p :=
    D.filtration.coordinateQuotientModel_geometry F.basis F.weight F.layers I hI S hspan
      D.lattice F.grid F.grid_pos F.inner F.outer hp
      (by simpa only [Fintype.card_fin] using hF.1) hF.2.1 hF.2.2.1
  refine ⟨_, ?_, Q, U, rfl, rfl, rfl, ⟨hQ, ?_⟩, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => i ∉ S)
  · intro i j a k
    exact (hb i j a k).trans hp
  · intro i j
    exact rationalLogHeight_le_of_height
      (quotientFinBasis_projection_height F.basis I S hspan i j) (by norm_num)

  · intro j
    exact ⟨((Fintype.equivFin {i // i ∉ S}).symm j).val,
      fun x => quotientFinBasis_repr_mk F.basis I S hspan x j⟩

end RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))

theorem terminal_le_topRankIdeal :
    D.filtration.layer (s + 1) ≤ (R.filtration.layerIdeal s (r + 1)).toSubmodule := by
  rw [D.filtration.terminal]
  exact bot_le

theorem exists_controlled_lower_rank_quotient {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    let I := R.filtration.layerIdeal s (r + 1)
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        ∃ U : Q.DegreeRankStructure r,
          U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
          Q.filtration = D.filtration.quotientLie I R.terminal_le_topRankIdeal ∧
          Q.lattice = D.lattice.map (D.filtration.quotientStepHom I R.terminal_le_topRankIdeal) ∧
          U.ComplexityLE ((p + 3) ^ 11) ∧
          ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 3) ^ 5 := by
  intro I
  obtain ⟨F, hF, _, hinv⟩ := R.exists_rank_adapted_data hp hR
  obtain ⟨n, hn, Q, U, hU, hQF, hQL, hUc, _, hcoord⟩ :=
    F.exists_lower_rank_quotient (by positivity : 0 ≤ (p + 3) ^ 11) hF.1
  have hdim : finrank ℚ L = d := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  refine ⟨n, hdim ▸ hn, Q, U, hU, hQF, hQL, hUc, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := hcoord j
  rw [hk]
  exact hinv i k

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d n : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
  (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientLie
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) {w : σ → ℕ}

noncomputable def rankQuotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

theorem rankQuotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (R.rankQuotientOrbit Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))
        (D.filtration.realification.polynomialOrbitEval w x g) :=
  D.filtration.realQuotientPolynomialOrbit_eval
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal g x

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_native_positive_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (E.realLattice ⊓ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
        D.realLattice.map (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
      (letI := D.metricSpace; LipschitzWith ℓ u) →
      (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
      (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∃ (v : E.Space → ℂ) (K : ℝ≥0),
        (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := E.metricSpace; LipschitzWith K v) ∧
        (∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) ∧ (∀ y, ‖v y‖ ≤ 1) ∧
        ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨c, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ hcover u ℓ hℓ hu hunit hker
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHt : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have ht : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hpt : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr hpt
  have hub : ∀ x, ‖u x‖ ≤ (1 : ℝ≥0) := by
    intro x
    rw [← positiveClip_eq_self (u x) (hunit x)]
    exact norm_positiveClip_le_one _
  let := E.metricSpace
  obtain ⟨v, K, hK, hv, _, heval⟩ := hrec D.filtration.lowerCentralSeries_eq_bot
    E.filtration.lowerCentralSeries_eq_bot D.basis E.basis φ D.lattice E.lattice
    D.grid E.grid H D.grid_pos E.grid_pos hH D.outer_grid E.inner_grid E.outer_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (fun i j => rationalHeightLE_ceil_exp (hφ i j)) hcover u hker ℓ 1 hu hub
    (p + 1) ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt)
    hHt (hE.2.1.trans hexp) (hℓ.trans hexp) (by simpa only [NNReal.coe_one] using Real.one_le_exp ht)
  obtain ⟨v', hv', hunit', hcap', heval'⟩ := exists_positive_lipschitz_reconstruction
    (fun x : D.RealGroup => u (QuotientGroup.mk x)) (fun x => hunit (QuotientGroup.mk x))
    (fun x => (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ x) : E.Space)) v hv heval
  have hcost : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨v', K, hK.trans (Real.exp_le_exp.mpr hcost), hv', hunit', hcap', heval'⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_uniform_native_positive_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ℓ u) →
            (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
            (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
              u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
            ∃ (v : Q.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := Q.metricSpace; LipschitzWith K v) ∧
              (∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) ∧ (∀ y, ‖v y‖ ≤ 1) ∧
              ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨a, _, hcover⟩ := exists_native_image_cover s
  obtain ⟨b, _, hrec⟩ := exists_native_positive_reconstruction s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a
  let P := Q + (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hidx, N, hN, hin, hout, hQ, hLift⟩ :=
    hcover D E φ hp hD hE hφ
  let q := p + (p + a) ^ a
  have hpq : p ≤ q := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)
  have hq : 0 ≤ q := hp.trans hpq
  have hBq : (p + a) ^ a ≤ q := le_add_of_nonneg_left hp
  have hbound : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hq (Nat.cast_nonneg b)) _)).trans hbound
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hidx.trans (Real.exp_le_exp.mpr (hBq.trans hqC)), N, hN, hin, hout,
    hQ.mono _ (hBq.trans hqC), ?_⟩
  intro u ℓ hℓ hu hunit hker
  obtain ⟨v, K, hK, hv, hunit', hcap, heval⟩ := hrec D (E.withLattice Λ N hN hin hout) φ hq
    (hD.mono D hpq) (hQ.mono _ hBq) (fun i j => (hφ i j).trans hpq) hLift
    u ℓ (hℓ.trans (Real.exp_le_exp.mpr hpq)) hu hunit hker
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hunit', hcap, heval⟩

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

theorem exists_uniform_positive_frozen_observable (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (u : E.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := E.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              ∃ (v : Q.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := Q.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : Q.RealGroup, v (QuotientGroup.mk x) = u (QuotientGroup.mk
                  (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr u ℓ hℓ hu hunit
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  obtain ⟨v, hv, hunitv, hcap, heval⟩ :=
    Q.exists_positive_frozen_observable E φ a r hconj hBLip ha' u hu hunit
  refine ⟨v, ℓ * (A * B), ?_, hv, hunitv, hcap, heval⟩
  calc
    _ = (ℓ : ℝ) * ((A : ℝ) * B) := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp p * (Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2)) :=
      mul_le_mul hℓ (mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le)
        (mul_nonneg A.coe_nonneg B.coe_nonneg) (Real.exp_pos p).le
    _ = Real.exp (p + (t + c₁) ^ c₁ + (t + 2) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hcostC

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M N : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] N)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] N)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] N)] [T2Space (ℝ ⊗[ℚ] N)]
      {d e f : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (T : RationalFilteredNilmanifold N s f) (φ : L →ₗ⁅ℚ⁆ M) (ψ : L →ₗ⁅ℚ⁆ N) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p → T.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (T.basis.repr (ψ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
          (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
          let V := T.withLattice Λ B hB hin hout
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (u : E.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := E.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              (∀ z ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x : D.RealGroup,
                u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
              ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := V.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : D.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := T.filtration.lowerCentralSeries_eq_bot) ψ x)) =
                  u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨a₀, _, hfreeze⟩ := exists_uniform_positive_frozen_observable s k
  obtain ⟨b₀, _, hrec⟩ := exists_uniform_native_positive_reconstruction s
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a₀) ^ a₀
  let P := R + (R + Polynomial.C b₀) ^ b₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e f D E T φ ψ p hp hD hE hT hφ hψ q hq hqp
  obtain ⟨Γ, _, _, _, _, _, A, hA, hAin, hAout, hQ, hfrozen⟩ :=
    hfreeze D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Γ A hA hAin hAout
  let t := p + (p + a₀) ^ a₀
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a₀)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hQt : (p + a₀) ^ a₀ ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + b₀) ^ b₀ ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + b₀) ^ b₀ ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hBin, hBout, hV, hreconstruct⟩ :=
    hrec Q T ψ ht (hQ.mono Q hQt) (hT.mono T hpt) (fun i j => (hψ i j).trans hpt)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcost),
    B, hB, hBin, hBout, hV.mono _ hcost, ?_⟩
  intro a r ha hr u ℓ hℓ hu hunit hkernel
  obtain ⟨w, K₀, hK₀, hw, hunitw, _, hevalw⟩ := hfrozen a r ha hr u ℓ hℓ hu hunit
  have hker : ∀ z ∈ (realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
      (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x,
      w (QuotientGroup.mk (z * x)) = w (QuotientGroup.mk x) := by
    intro z hz x
    rw [hevalw, hevalw]
    exact hkernel z hz x
  obtain ⟨v, K, hK, hv, hunitv, hcap, hevalv⟩ := hreconstruct w K₀
    (hK₀.trans (Real.exp_le_exp.mpr hQt)) hw hunitw hker
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hunitv, hcap,
    fun x => (hevalv x).trans (hevalw x)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let T := nativeRefilteredTarget D a W E Q
  let N := ∀ j : Option {i : ι // i ≠ a}, optionLieSpace
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1))
    (fun i : {i : ι // i ≠ a} => L i.val) j
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  letI := realification_moduleTopology_t2 T.basis
  ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
    (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
    (Λ.subgroupOf T.lattice).FiniteIndex ∧
    (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
    ∃ (B : ℕ) (hB : 0 < B)
      (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
      (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
      let V := T.withLattice Λ B hB hin hout
      V.GeometryComplexityLE cost ∧
      ∀ {J : Type u} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (eta j)) x = 0) →
        ∀ l r : (D a).RealGroup,
          (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := (D a).metricSpace; LipschitzWith ℓ S) →
            (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
            (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
            ∃ (v : V.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp cost ∧
              (letI := V.metricSpace; LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              (∀ x, ‖v x‖ ≤ 1) ∧ ∀ x : E.RealGroup,
              v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := T.filtration.lowerCentralSeries_eq_bot) (nativeRefilteredMap D a W E) x)) =
              S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := (D a).filtration.lowerCentralSeries_eq_bot)
                (refilteredComponentMap D W a) x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def LowerRefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I, L i.val) (s + 1)
        (Fintype.card (Σ i : I, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      ∀ {J : Type u} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (eta j)) x = 0) →
        ∀ l r : (D a).RealGroup,
          (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := (D a).metricSpace; LipschitzWith ℓ S) →
            (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
            (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
            ∃ (v : Q'.Space × Z.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp cost ∧
              (letI := Q'.metricSpace; letI := Z.metricSpace; LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              ∀ x : E.RealGroup,
                v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := Q'.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x),
                  QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := Z.filtration.lowerCentralSeries_eq_bot)
                    (liePiMap (fun i : I => refilteredComponentMap D W i.val)) x)) =
                  S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := (D a).filtration.lowerCentralSeries_eq_bot)
                    (refilteredComponentMap D W a) x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

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

noncomputable def LowerRefilteredCyclicExpansionSpec
    (p : ℝ) (q k : ℕ) (cost : ℝ) (C : ℕ) : Prop :=
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
          (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) {ρ η : ℝ},
          0 < ρ → 0 ≤ η →
          (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
          (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
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
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) (slow h)) →
              (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
              ∀ (anchor : I → ZMod N → ℝ) (r₀ : I → ZMod N → (D a).RealGroup),
                (∀ i h, |anchor i h| ≤ N) →
                (∀ i h b, |((D a).basis.baseChange ℝ).repr
                  ((D a).filtration.adaptedPolynomialRealValueHom w (fun _ => anchor i h) (slow h)).coord b| ≤
                    Real.exp ((p + 2) ^ k)) →
                (∀ i h, ((D a).basis.baseChange ℝ).equivFun (r₀ i h).coord ∈ realDenominatorGrid q) →
                (∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
                  |(x.val : ℝ) - anchor i h| ≤ (N : ℝ) * ρ) →
                (∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
                  (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w
                    (fun _ => (x.val : ℝ)) (rat h)) : (D a).Space) = QuotientGroup.mk (r₀ i h)) →
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
                    ∀ h, (𝔼 x, |err h x|) ≤
                      Real.exp ((p + C) ^ C) * ρ + Real.exp cost * η + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open scoped TensorProduct

theorem realificationMap_id_eq_changeStep {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s t : ℕ} (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) :
    (realificationMap (hnil := hs) (hM := ht) (LieHom.id : L →ₗ⁅ℚ⁆ L) : _ → _) =
      (changeStep (realification_lowerCentralSeries_eq_bot hs)
        (realification_lowerCentralSeries_eq_bot ht) : _ → _) := by
  funext x
  apply ext
  exact realificationLieHom_id_apply x.coord

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

noncomputable def loweredCoverMap :
    (D.loweredCover hst Λ N hN hin hout).Space →
      ((D.raiseStep hst).withLattice Λ N hN hin hout).Space :=
  cosetMap (D.loweredCover hst Λ N hN hin hout).realLattice
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L) (D.lowerCoverLattice hst Λ) Λ
      (D.lowerCoverLattice_forward hst Λ))

theorem loweredCoverMap_mk (x : (D.loweredCover hst Λ N hN hin hout).RealGroup) :
    D.loweredCoverMap hst Λ N hN hin hout (QuotientGroup.mk x) =
      QuotientGroup.mk (changeStep D.filtration.realification.lowerCentralSeries_eq_bot
        (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot x) := by
  change QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) = _
  rw [realificationMap_id_eq_changeStep]

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem loweredCoverMap_lipschitz :
    letI := (D.loweredCover hst Λ N hN hin hout).metricSpace
    letI := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace
    LipschitzWith 1 (D.loweredCoverMap hst Λ N hN hin hout) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
    rw [realificationMap_id_eq_changeStep]
    exact lipschitz_changeStep (D.basis.baseChange ℝ) _ _
  exact lipschitz_cosetMap (D.loweredCover hst Λ N hN hin hout).realLattice
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice
    (D.loweredCover hst Λ N hN hin hout).realLattice_closed_discrete.1
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice_closed_discrete.1
    _ _ hLip

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L Z : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
  (v : ((D.raiseStep hst).withLattice Λ N hN hin hout).Space × Z → ℂ)

noncomputable def loweredCoverPullback : (D.loweredCover hst Λ N hN hin hout).Space × Z → ℂ :=
  fun y => v (D.loweredCoverMap hst Λ N hN hin hout y.1, y.2)

theorem loweredCoverPullback_mk (x : D.RealGroup) (z : Z) :
    D.loweredCoverPullback hst Λ N hN hin hout v (QuotientGroup.mk x, z) =
      v (QuotientGroup.mk (changeStep D.filtration.realification.lowerCentralSeries_eq_bot
        (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot x), z) := by
  unfold loweredCoverPullback
  rw [D.loweredCoverMap_mk]

theorem loweredCoverPullback_bounds
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [PseudoMetricSpace Z]
    {K : ℝ≥0}
    (hv : letI := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace; LipschitzWith K v)
    (hpositive : ∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) :
    letI := (D.loweredCover hst Λ N hN hin hout).metricSpace
    LipschitzWith K (D.loweredCoverPullback hst Λ N hN hin hout v) ∧
      ∀ y, (D.loweredCoverPullback hst Λ N hN hin hout v y).im = 0 ∧
        0 ≤ (D.loweredCoverPullback hst Λ N hN hin hout v y).re ∧
        (D.loweredCoverPullback hst Λ N hN hin hout v y).re ≤ 1 := by
  let := (D.loweredCover hst Λ N hN hin hout).metricSpace
  let := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace
  have hm := ((D.loweredCoverMap_lipschitz hst Λ N hN hin hout).comp
    (LipschitzWith.prod_fst (β := Z))).prodMk
      (LipschitzWith.prod_snd (α := (D.loweredCover hst Λ N hN hin hout).Space))
  have hpair : LipschitzWith 1 (fun y : (D.loweredCover hst Λ N hN hin hout).Space × Z =>
      (D.loweredCoverMap hst Λ N hN hin hout y.1, y.2)) := by
    simpa only [mul_one, max_self, Function.comp_def] using hm
  refine ⟨?_, fun y => hpositive _⟩
  unfold loweredCoverPullback
  simpa only [mul_one, Function.comp_def] using hv.comp hpair

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_split_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      {s : ℕ} {d : Option ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ) (hm : 0 < m)
      (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ)
      (hΛout : bchSubgroupCoordinates (pi D).basis Λ ⊆ denominatorGrid m)
      {p : ℝ}, 0 ≤ p → (Fintype.card (Option ι) : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : Option ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        ∃ _hsub : (pi E).lattice ≤ Λ,
          (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
            ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
            ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          (pi E).GeometryComplexityLE ((p + C) ^ C) ∧
          (pi (fun i => E (some i))).GeometryComplexityLE ((p + C) ^ C) ∧
          let V := (pi D).withLattice Λ m hm hΛin hΛout
          ∀ (u : V.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := V.metricSpace; LipschitzWith ℓ u) →
            (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
            ∃ (v : (E none).Space × (pi (fun i => E (some i))).Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (letI := (E none).metricSpace
               letI := (pi (fun i => E (some i))).metricSpace
               LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              ∀ x : (pi E).RealGroup,
                v (optionProductSpaceEquiv E (QuotientGroup.mk x)) = u (QuotientGroup.mk x) := by
  obtain ⟨A, _, hcover⟩ := exists_native_factorwise_covers
  obtain ⟨B, _, hmetric⟩ := exists_optionProductMetric_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + 2) ^ 2 + X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ s d D Λ m hm hΛin hΛout p hp hι hD hmp
  obtain ⟨Δ, N, hN, hin, hout, hindex, hE, hprod, hsub⟩ :=
    hcover D Λ m hm hΛin hp hι hD hmp
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let V := (pi D).withLattice Λ m hm hΛin hΛout
  let t := p + (p + A) ^ A
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hsum : t + (t + 2) ^ 2 + p + (p + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htc : t ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (t + 2), pow_nonneg (show 0 ≤ p + B by positivity) B]
  have hrestc : (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + B by positivity) B]
  have hlipc : p + (p + B) ^ B ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (t + 2)]
  have hι' : (Fintype.card ι : ℝ) ≤ t := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hι
    linarith
  have hrest := pi_geometry (fun i => E (some i)) (hp.trans hpt) hι'
    (fun i => (hE (some i)).mono _ hAt)
  refine ⟨Δ, N, hN, hin, hout, hsub, ?_, fun i => (hE i).mono _ (hAt.trans htc),
    hprod.mono _ (hAt.trans htc), hrest.mono _ hrestc, ?_⟩
  · intro i
    obtain ⟨hle, hc, hn, hf, hi⟩ := hindex i
    exact ⟨hle, hc, hn, hf, hi.trans (Real.exp_le_exp.mpr (hAt.trans htc))⟩
  · dsimp only
    intro u ℓ hℓ hu hpositive
    let M := (1 + productMetricBound (fun i => d (some i))) * productMetricBound d
    have hM : (M : ℝ) ≤ Real.exp ((p + B) ^ B) := hmetric d hp hι (fun i => (hD i).1)
    have hK : ((ℓ * M : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
      calc
        _ ≤ Real.exp p * Real.exp ((p + B) ^ B) := by push_cast; gcongr
        _ = Real.exp (p + (p + B) ^ B) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlipc
    obtain ⟨hLip, hunit, heval⟩ := splitCoverProjection_pullback E V hsub rfl u hu hpositive
    exact ⟨u ∘ splitCoverProjection E V hsub, ℓ * M, hK, hLip, hunit, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_lowered_split_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] [DecidableEq ι]
      {L₀ : Type u} {L : ι → Type u}
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {s t d₀ : ℕ} {d : ι → ℕ} (Q : RationalFilteredNilmanifold L₀ s d₀) (hst : s ≤ t)
      (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i)),
      let F := optionFactors (Q.raiseStep hst) D
      ∀ (Λ : Subgroup (pi F).filtration.Group) (m : ℕ) (hm : 0 < m)
        (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi F).basis Λ)
        (hΛout : bchSubgroupCoordinates (pi F).basis Λ ⊆ denominatorGrid m) {p : ℝ},
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → Q.GeometryComplexityLE p →
        (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
        ∃ (Δ : ∀ i, Subgroup (F i).filtration.Group) (N : Option ι → ℕ)
          (hN : ∀ i, 0 < N i)
          (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (F i).basis (Δ i))
          (hout : ∀ i, bchSubgroupCoordinates (F i).basis (Δ i) ⊆ denominatorGrid (N i)),
          let E := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
          let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hin none) (hout none)
          ∃ _hsub : (pi E).lattice ≤ Λ,
            (∀ i, Δ i ≤ (F i).lattice ∧ ((Δ i).subgroupOf (F i).lattice).Characteristic ∧
              ((Δ i).subgroupOf (F i).lattice).Normal ∧ ((Δ i).subgroupOf (F i).lattice).FiniteIndex ∧
              ((Δ i).relIndex (F i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            Q'.filtration = Q.filtration ∧ Q'.lattice ≤ Q.lattice ∧
            Q'.GeometryComplexityLE ((p + C) ^ C) ∧
            (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
            (pi (fun i => E (some i))).GeometryComplexityLE ((p + C) ^ C) ∧
            let V := (pi F).withLattice Λ m hm hΛin hΛout
            ∀ (u : V.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := V.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              ∃ (v : Q'.Space × (pi (fun i => E (some i))).Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace
                 letI := (pi (fun i => E (some i))).metricSpace
                 LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : (pi E).RealGroup,
                  v (QuotientGroup.mk (changeStep (E none).filtration.realification.lowerCentralSeries_eq_bot
                      Q.filtration.realification.lowerCentralSeries_eq_bot (productProjectionHom E none x)),
                    (optionProductSpaceEquiv E (QuotientGroup.mk x)).2) = u (QuotientGroup.mk x) := by
  obtain ⟨A, _, hsplit⟩ := exists_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 1 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L₀ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s t d₀ d Q hst D F Λ m hm hΛin hΛout p hp hι hQ hD hmp
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := fun i =>
    match i with
    | none => inferInstance
    | some i => inferInstance
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  let : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  let : ∀ i, T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  have hpp : p ≤ p + 1 := by linarith
  have hF : ∀ i, (F i).GeometryComplexityLE (p + 1) := by
    intro i
    cases i with
    | none => exact (Q.raiseStep_geometry hst hQ).mono _ hpp
    | some i => exact (hD i).mono _ hpp
  obtain ⟨Δ, N, hN, hin, hout, hsub, hindex, hE, _, hrest, hrec⟩ :=
    hsplit F Λ m hm hΛin hΛout (by linarith : 0 ≤ p + 1)
      (by simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]; linarith)
      hF (hmp.trans (Real.exp_le_exp.mpr hpp))
  let E := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hin none) (hout none)
  have hsum : p + (p + 1 + A) ^ A ≤ (p + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) A)).trans hsum
  have hcost : (p + 1 + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_left hp).trans hsum
  have hlow : Q'.GeometryComplexityLE ((p + C) ^ C) :=
    Q.loweredCover_geometry hst (Δ none) (N none) (hN none) (hin none) (hout none) hQ hpC
      ((hE none).2.1.trans (Real.exp_le_exp.mpr hcost))
  refine ⟨Δ, N, hN, hin, hout, hsub, ?_, rfl,
    Q.lowerCoverLattice_le hst (Δ none) (hindex none).1, hlow,
    fun i => (hE i).mono _ hcost, hrest.mono _ hcost, ?_⟩
  · intro i
    obtain ⟨hle, hc, hn, hf, hi⟩ := hindex i
    exact ⟨hle, hc, hn, hf, hi.trans (Real.exp_le_exp.mpr hcost)⟩
  · dsimp only
    intro u ℓ hℓ hu hpositive
    obtain ⟨v, K, hK, hv, hunit, heval⟩ := hrec u ℓ
      (hℓ.trans (Real.exp_le_exp.mpr hpp)) hu hpositive
    let := (pi (fun i => E (some i))).metricSpace
    obtain ⟨hLip, hpos⟩ := Q.loweredCoverPullback_bounds hst (Δ none) (N none)
      (hN none) (hin none) (hout none) v hv hunit
    refine ⟨Q.loweredCoverPullback hst (Δ none) (N none) (hN none) (hin none) (hout none) v,
      K, hK.trans (Real.exp_le_exp.mpr hcost), hLip, hpos, ?_⟩
    intro x
    have h := Q.loweredCoverPullback_mk hst (Δ none) (N none) (hN none) (hin none) (hout none) v
      (changeStep (E none).filtration.realification.lowerCentralSeries_eq_bot
        Q.filtration.realification.lowerCentralSeries_eq_bot (productProjectionHom E none x))
      (optionProductSpaceEquiv E (QuotientGroup.mk x)).2
    apply h.trans
    change v ((optionProductSpaceEquiv E (QuotientGroup.mk x)).1,
      (optionProductSpaceEquiv E (QuotientGroup.mk x)).2) = u (QuotientGroup.mk x)
    simpa only [Prod.mk.eta] using heval x

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace optionDimension

theorem exists_uniform_frozen_two_target_reconstruction (t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H M L₀ L₁ : Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
      {s e f d₀ d₁ : ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀) (_hst : s ≤ t)
      (F₁ : RationalFilteredNilmanifold L₁ t d₁)
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ₁ : H →ₗ⁅ℚ⁆ L₁) {p : ℝ},
      1 ≤ p →
      E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      F₁.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (ψ₀ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (F₁.basis.repr (ψ₁ (E.basis j)) i) ≤ p) →
      Function.Injective (optionProductMap ψ₀ (fun _ : Unit => ψ₁)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ F' : RationalFilteredNilmanifold L₁ t d₁,
          F'.filtration = F₁.filtration ∧ F'.basis = F₁.basis ∧ F'.lattice ≤ F₁.lattice ∧
          F'.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              ∃ (v : Q'.Space × F'.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace; letI := F'.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : E.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x),
                    QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := F'.filtration.lowerCentralSeries_eq_bot) ψ₁ x)) =
                    S (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨A, _, hfrozen⟩ := exists_uniform_frozen_reconstruction t k
  obtain ⟨B, _, hsplit⟩ := exists_lowered_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 3) ^ 2
  let P₁ := P₀ + (P₀ + Polynomial.C A) ^ A
  let P₂ := P₁ + (P₁ + Polynomial.C B) ^ B + (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₂
  refine ⟨C, hC, ?_⟩
  intro H M L₀ L₁ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s e f d₀ d₁ E D Q hst F₁ φ ψ₀ ψ₁ p hpone hE hD hQ hF₁ hφ hψ₀ hψ₁ hψinj q hq hqp
  have hp : 0 ≤ p := le_trans zero_le_one hpone
  let F := fun _ : Unit => F₁
  let ψ := fun _ : Unit => ψ₁
  have hι : (Fintype.card Unit : ℝ) ≤ p := by simpa using hpone
  have hF : ∀ i, (F i).GeometryComplexityLE p := fun _ => hF₁
  have hψ : ∀ a i j, rationalLogHeight ((F a).basis.repr (ψ a (E.basis j)) i) ≤ p :=
    fun _ => hψ₁
  let Z₀ := pi F
  let T := optionProduct (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Unit → L₁))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (Unit → L₁))
  let := realification_moduleTopology_t2 Z₀.basis
  let Mprod := ∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i
  let Aprod := optionFactors (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Mprod)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] Mprod)
  let := realification_moduleTopology_t2 T.basis
  let p₀ := (p + 3) ^ 2
  let p₁ := p₀ + (p₀ + A) ^ A
  have hp₀ : 0 ≤ p₀ := sq_nonneg _
  have hpp₀ : p ≤ p₀ := by dsimp only [p₀]; nlinarith [sq_nonneg p]
  have hp₀p₁ : p₀ ≤ p₁ := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hp₁ : 0 ≤ p₁ := hp₀.trans hp₀p₁
  have hAp₁ : (p₀ + A) ^ A ≤ p₁ := le_add_of_nonneg_left hp₀
  have hsum : p₁ + (p₁ + B) ^ B + (p + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P₂, P₁, P₀, X, p₀, p₁, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p₁ + B) ^ B ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (p + 2)]
  have htotal : (p₁ + B) ^ B + (p + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hT : T.GeometryComplexityLE p₀ :=
    optionProduct_geometry (Q.raiseStep hst) F hp hι (Q.raiseStep_geometry hst hQ) hF
  have hmap : ∀ i j, rationalLogHeight (T.basis.repr (optionProductMap ψ₀ ψ (E.basis j)) i) ≤ p₀ := by
    intro i j
    exact (optionProductMap_logHeight (Q.raiseStep hst) F E.basis ψ₀ ψ hψ₀ hψ i j).trans hpp₀
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin, hout, hV, hrec⟩ :=
    hfrozen E D T φ (optionProductMap ψ₀ ψ) p₀ hp₀ (hE.mono E hpp₀)
      (hD.mono D hpp₀) hT (fun i j => (hφ i j).trans hpp₀) hmap q hq
      (hqp.trans (Real.exp_le_exp.mpr hpp₀))
  obtain ⟨Δ, N, hN, hNin, hNout, _, hindex, hQfil, hQle, hQgeom, hGgeom, hZgeom, hsplitrec⟩ :=
    hsplit Q hst F Λ m hm hin hout hp₁ (hι.trans (hpp₀.trans hp₀p₁))
      (hQ.mono Q (hpp₀.trans hp₀p₁))
      (fun i => (hF i).mono (F i) (hpp₀.trans hp₀p₁))
      (hV.2.1.trans (Real.exp_le_exp.mpr hAp₁))
  let G := fun i => (Aprod i).withLattice (Δ i) (N i) (hN i) (hNin i) (hNout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hNin none) (hNout none)
  let F' : RationalFilteredNilmanifold L₁ t d₁ := G (some ())
  let Z := pi (fun _ : Unit => F')
  refine ⟨Q', hQfil, rfl, hQle, hQgeom.mono Q' hcost,
    F', rfl, rfl, (hindex (some ())).1, (hGgeom (some ())).mono F' hcost, ?_⟩
  intro a r ha hr S ℓ hℓ hS hpositive
  have hkernel := frozenDiagramKernelInvariance_of_injective E D T φ (optionProductMap ψ₀ ψ)
    hψinj S a r
  have ha₀ : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p₀ + 2) ^ k) := by
    intro i
    exact (ha i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨u, K₀, hK₀, hu, hunit, _, heval⟩ := hrec a r ha₀ hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp₀)) hS hpositive hkernel
  obtain ⟨v, K, hK, hv, hpos, hveval⟩ :=
    hsplitrec u K₀ (hK₀.trans (Real.exp_le_exp.mpr hAp₁)) hu hunit
  let := Q'.metricSpace
  let := F'.metricSpace
  let := Z.metricSpace
  let L : ℝ≥0 := max 1 (productMetricBound (fun _ : Unit => d₁))
  let v' : Q'.Space × F'.Space → ℂ := fun z => v (z.1, F'.singletonProductSpace z.2)
  have hmapLip : LipschitzWith L (fun z : Q'.Space × F'.Space =>
      (z.1, F'.singletonProductSpace z.2)) := by
    have h := (LipschitzWith.prod_fst (β := F'.Space)).prodMk
      (F'.singletonProductSpace_lipschitz.comp
        (LipschitzWith.prod_snd (α := Q'.Space)))
    simpa only [mul_one, Function.comp_def, optionDimension, L] using h
  have hL : (L : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    exact max_le (Real.one_le_exp (sq_nonneg _))
      (productMetricBound_singleton_le_exp hp hF₁.1)
  have hKL : (K * L : ℝ≥0) ≤ Real.exp ((p + C) ^ C) := by
    calc
      (K * L : ℝ≥0) = (K : ℝ) * (L : ℝ) := NNReal.coe_mul K L
      _ ≤ Real.exp ((p₁ + B) ^ B) * Real.exp ((p + 2) ^ 2) :=
        mul_le_mul hK hL (NNReal.coe_nonneg L) (Real.exp_nonneg _)
      _ = Real.exp ((p₁ + B) ^ B + (p + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr htotal
  refine ⟨v', K * L, hKL, hv.comp hmapLip, fun z => hpos _, ?_⟩
  intro x
  dsimp only [v', Prod.fst, Prod.snd]
  rw [F'.singletonProductSpace_realificationMap E.filtration ψ₁ x]
  let maps := optionMaps ψ₀ ψ
  let y : (pi G).RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi G).filtration.lowerCentralSeries_eq_bot) (liePiMap maps) x
  have hfirst := lowered_productProjectionHom_realificationMap E.filtration G Q maps x
  have hsecond := congrArg Prod.snd (optionProductSpaceEquiv_realificationMap E.filtration G maps x)
  have hargs := congrArg₂ Prod.mk
    (congrArg (QuotientGroup.mk : Q'.RealGroup → Q'.Space) hfirst.symm) hsecond.symm
  exact (congrArg v hargs).trans ((hveval y).trans (heval x))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

section Conclusion

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]

def AllocatedMarkedDiagramRecoveryCovers (k q : ℕ) (p cost : ℝ) : Prop :=
  ∃ Q' : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ F' : RationalFilteredNilmanifold
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF,
      F'.filtration = Fref.filtration ∧ F'.basis = Fref.basis ∧ F'.lattice ≤ Fref.lattice ∧
      F'.GeometryComplexityLE cost ∧
      let K : ℝ≥0 := ⟨Real.exp cost, (Real.exp_pos _).le⟩
      letI := Q'.metricSpace
      letI := F'.metricSpace
      let diagram := Dref.markedTopQuotientDiagram F'
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q'
      ∀ a r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
        ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
          (letI := D.metricSpace; LipschitzWith ℓ S) →
          (∀ y, (S y).im = 0 ∧ 0 ≤ (S y).re ∧ (S y).re ≤ 1) →
          let frozen := fun x : Dref.RealGroup => S (QuotientGroup.mk
            (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra W).incl x * r))
          ∀ x : Dref.RealGroup,
            positiveImageSlice diagram K frozen (diagram x).2 (diagram x).1 = frozen x

end Conclusion

theorem exists_allocated_marked_diagram_recovery_covers (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type u}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d f nD nF nQ : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (Dref : RationalFilteredNilmanifold
        (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
      (_hDref : Dref.filtration = D.filtration.gradedRefiltration W)
      (Fref : RationalFilteredNilmanifold
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))] {p : ℝ},
      1 ≤ p → Dref.GeometryComplexityLE p → D.GeometryComplexityLE p →
      Q.GeometryComplexityLE p → Fref.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (Dref.basis j : L) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Fref.basis.repr
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis j)) i) ≤ p) →
      (∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        AllocatedMarkedDiagramRecoveryCovers D Fmark φ hφ W Dref Fref Q k q p ((p + C) ^ C) := by
  obtain ⟨C, hC, hconstruct⟩ := exists_uniform_frozen_two_target_reconstruction (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d f nD nF nQ D Fmark φ hφ W Dref hDref Fref Q
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp hDrefGeom hDGeom hQGeom hFrefGeom
    hinc hquot hmark hker q hq hqp
  obtain ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, hrec⟩ :=
    hconstruct Dref D Q (Nat.le_succ s) Fref
      (D.filtration.gradedRefiltrationSubalgebra W).incl
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      hp hDrefGeom hDGeom hQGeom hFrefGeom hinc hquot hmark
      (D.allocatedMarkedDiagram_injective_of_top_kernel Fmark φ hφ W Dref hDref hker)
      q hq hqp
  refine ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, ?_⟩
  let K : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), (Real.exp_pos _).le⟩
  let := Q'.metricSpace
  let := F'.metricSpace
  dsimp only
  intro a r ha hr S ℓ hℓ hS hpositive x
  obtain ⟨v, Lrec, hLrec, hv, _, heval⟩ := hrec a r ha hr S ℓ hℓ hS hpositive
  have hL : Lrec ≤ K := hLrec
  refine positiveImageSlice_eq _ _ _ (fun x => hpositive _) ?_ x
  intro y z
  have h := (hv.weaken hL).dist_le_mul
    (Dref.markedTopQuotientDiagram F'
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q' y)
    (Dref.markedTopQuotientDiagram F'
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q' z)
  simpa only [dist_eq_norm, markedTopQuotientDiagram, heval] using h

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

section Conclusion

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem NativeGridRightDictionary.markedTopQuotient_recovery
    {inputDenominator : ℕ} {bound : ℝ}
    (dictionary : D.NativeGridRightDictionary inputDenominator bound)
    (K : ℝ≥0) (observable : D.Space → ℂ) (a r : D.RealGroup)
    (hr : (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid inputDenominator)
    (hrecovery :
      letI := Q.metricSpace
      letI := Fref.metricSpace
      let diagram := Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
      ∀ j : Fin dictionary.count,
        let frozen := fun source : Dref.RealGroup => observable (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl source * dictionary.representative j))
        ∀ source, positiveImageSlice diagram K frozen
          (diagram source).2 (diagram source).1 = frozen source) :
    letI := Q.metricSpace
    letI := Fref.metricSpace
    let diagram := Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
    let frozen := fun source : Dref.RealGroup => observable (QuotientGroup.mk
      (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source * r))
    ∀ source, positiveImageSlice diagram K frozen
      (diagram source).2 (diagram source).1 = frozen source := by
  let := Q.metricSpace
  let := Fref.metricSpace
  dsimp only at hrecovery ⊢
  obtain ⟨label, hlabel⟩ := dictionary.labeling (fun _ : Unit => r) (fun _ => hr)
  let inclusion : Dref.RealGroup → D.RealGroup :=
    realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl
  have hfrozen : (fun source : Dref.RealGroup => observable (QuotientGroup.mk
        (a * inclusion source * r))) =
      (fun source : Dref.RealGroup => observable (QuotientGroup.mk
        (a * inclusion source * dictionary.representative (label ())))) := by
    funext source
    exact congrArg observable ((hlabel ()).2 (a * inclusion source))
  change ∀ source, positiveImageSlice
    (Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (fun x => observable (QuotientGroup.mk (a * inclusion x * r)))
    ((Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) source).2
    ((Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) source).1 =
      (fun x => observable (QuotientGroup.mk (a * inclusion x * r))) source
  rw [hfrozen]
  exact hrecovery (label ())

end Conclusion

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TopInvariantIntegerExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_topInvariant_integer_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) T.eval) := by
  obtain ⟨a, _, hdescent⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D w T p hp hT hinv
  let q := (p + 3) ^ 11
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + 3 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 1 ≤ 11)
  obtain ⟨n, _, Q, hQF, hQL, hQ, he, _⟩ := D.exists_controlled_top_quotient hp hT.1
  have heq : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ q := by
    intro i j
    apply (he j i).trans
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, _, hS, hSe⟩ := hdescent D Q hQF hQL T q hq (hT.mono hpq) hQ heq hinv
  have hfinal : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨NativeIntegerExpansion.ofTest S (hS.mono hfinal) (fun x => (hSe x).symm)⟩

noncomputable def topInvariantIntegerExponent (s : ℕ) : ℕ :=
  (exists_topInvariant_integer_expansion.{0} s).choose

theorem topInvariant_integer_expansion {L σ : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {w : σ → ℕ}
    (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x) :
    Nonempty (NativeIntegerExpansion w s
      ((p + topInvariantIntegerExponent s) ^ topInvariantIntegerExponent s) T.eval) :=
  (exists_topInvariant_integer_expansion s).choose_spec.2 D T hp hT hinv

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finiteCorrelation_one {A : Type*} (Q : Finset A) (u : A → ℂ) :
    ‖finiteCorrelation Q (fun _ => 1) u‖ = ‖𝔼 x ∈ Q, u x‖ := by
  have he : (𝔼 x ∈ Q, star (u x)) = star (𝔼 x ∈ Q, u x) := by
    simp [Finset.expect, star_sum]
  simp only [finiteCorrelation, one_mul, he, norm_star]

theorem finiteCorrelation_one_derivative {A : Type*} [AddCommGroup A]
    (Q : Finset A) (u : A → ℂ) (h : A) :
    finiteCorrelation Q (multiplicativeDerivative (fun _ : A => 1) h) (multiplicativeDerivative u h) =
      𝔼 x ∈ Q, u (x + h) * star (u x) := by
  simp only [finiteCorrelation, multiplicativeDerivative, star_one, one_mul, star_mul, star_star]

theorem exists_many_biased_box_shifts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i) (u : (ι → ℤ) → ℂ)
    {p : ℝ} (_hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hu : ∀ x ∈ translatedIntegerBox a T, ‖u x‖ ≤ Real.exp p)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox a T, u x‖) :
    ∃ H : Finset (ι → ℤ), H.Nonempty ∧
      Real.exp (-(4 * p + 6)) * (∏ i, (T i : ℝ)) ≤ H.card ∧
      ∀ h ∈ H,
        (∀ i, |(h i : ℝ)| ≤ T i) ∧
        (∀ i, Real.exp (-(5 * p + 6)) * T i < (((T i : ℤ) - |h i|).toNat : ℝ)) ∧
        Real.exp (-(2 * p + 1)) ≤
          ‖𝔼 x ∈ derivativeSupport (translatedIntegerBox a T) h, u (x + h) * star (u x)‖ := by
  classical
  let : ∀ i, NeZero (T i) := fun i => ⟨(hT i).ne'⟩
  let Q := translatedIntegerBox a T
  let δ := Real.exp (-(5 * p + 6))
  let P := fun h : ι → ℤ =>
    Real.exp (-p) ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative (fun _ : ι → ℤ => 1) h) (multiplicativeDerivative u h)‖ ∧
    δ * Q.card < ((derivativeSupport Q h).card : ℝ)
  let H := (cubeDifferenceSupport Q).filter P
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty T a
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Q (fun _ => 1) u‖ := by
    rw [norm_finiteCorrelation_one]
    exact hbias
  have hw := weight_correlating_large_box_overlaps a T (fun _ => 1) u
    (Real.exp_nonneg (-p)) (Real.exp_pos (p + 1)) (Real.exp_nonneg (-(5 * p + 6)))
    (fun _ _ => by norm_num) (fun x hx => (hu x hx).trans (Real.exp_le_exp.mpr (by linarith))) hcorr
  have hret := retained_exponential_weight (Fintype.card ι) (r := p) hι
  have hμ : Real.exp (-(4 * p + 6)) ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if P h then (1 : ℝ) else 0) := by
    have he₁ : 2 * p + 2 * p + 6 = 4 * p + 6 := by ring
    have he₂ : 4 * p + 6 + p = 5 * p + 6 := by ring
    have hret' : Real.exp (-(4 * p + 6)) ≤
        Real.exp (-p) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
          (2 : ℝ) ^ Fintype.card ι * Real.exp (-(5 * p + 6)) := by
      simpa only [he₁, he₂] using hret
    exact hret'.trans hw
  have hcount : Real.exp (-(4 * p + 6)) * (∏ i, (T i : ℝ)) ≤ H.card := by
    have hc := cardinality_ge_overlap_weight hQ (cubeDifferenceSupport Q) P hμ
    simpa only [H, Q, translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod] using hc
  have hnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < H.card :=
      (mul_pos (Real.exp_pos _) (Finset.prod_pos (fun i _ => by exact_mod_cast hT i))).trans_le hcount
    exact_mod_cast hpos
  refine ⟨H, hnonempty, hcount, ?_⟩
  intro h hh
  obtain ⟨hsupport, hc, hlarge⟩ := Finset.mem_filter.mp hh
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := box_overlap_length_pos a T hsupport i
    have habs : |h i| ≤ (T i : ℤ) := by omega
    exact_mod_cast habs
  · exact box_overlap_side_gt_of_card_gt a T hT h hlarge
  · have he : Real.exp (-p) ^ 2 = Real.exp (-2 * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsmall : Real.exp (-(2 * p + 1)) ≤ Real.exp (-p) ^ 2 / 2 := by
      have he' : -(2 * p + 1) = -2 * p - 1 := by ring
      rw [he, he']
      exact exp_sub_one_le_half_exp (-2 * p)
    rw [finiteCorrelation_one_derivative] at hc
    exact hsmall.trans hc

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_correlating_vertical_mode_preserving_characters (T : D.Niltest w)
    {p ρ : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
      U.ComplexityLE p ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
        ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ),
        (∀ x, T.observable (z • x) = c * T.observable x) →
          ∀ x, U.observable (z • x) = c * U.observable x) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation Q f U.eval‖ := by
  obtain ⟨J, inst, hdecomp⟩ := T.exists_controlled_vertical_decomposition hp hT
    (ρ / 2) (by linarith) hρp
  let := inst
  obtain ⟨η, U, hcard, hheight, hU, hchar, hint, hpres, _, herr⟩ := hdecomp
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f T.eval (fun j => (U j).eval)
    hρ (Real.exp_pos _) hcard hf (fun x _ => herr x) hcorr
  have hne : ∃ x, (U j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (U j).eval x = 0 := fun x => hzero _
    have hc0 : finiteCorrelation Q f (U j).eval = 0 := by simp [finiteCorrelation, heval]
    rw [hc0, norm_zero] at hj
    exact (not_le_of_gt (div_pos hρ (by positivity))) hj
  exact ⟨η j, U j, (hU j).1, (hU j).2, hheight j, hchar j, hint j hne,
    (fun z c hz x => hpres z c hz j x), hj⟩

theorem exists_correlating_vertical_mode (T : D.Niltest w)
    {p ρ : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
      U.ComplexityLE p ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
        ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation Q f U.eval‖ := by
  obtain ⟨η, U, hU, hOrbit, hheight, hchar, hint, _, hCorr⟩ :=
    T.exists_correlating_vertical_mode_preserving_characters hp hT hρ hρp hQ f hf hcorr
  exact ⟨η, U, hU, hOrbit, hheight, hchar, hint, hCorr⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_detection_vertical_mode (a : ℕ)
    (ha : ∀ q : ℝ, 0 ≤ q → verticalDecompositionBudget q ≤ (q + a) ^ a)
    (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w), U.ComplexityLE (p + 1) ∧
      Real.exp (-boxModeBudget a p) ≤ ‖finiteCorrelation Q f U.eval‖ ∧
      ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x := by
  have hp1 : 0 ≤ p + 1 := by linarith
  have herror : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div]; simp [Real.exp_neg]
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg p)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨η, U, hU, _, _, hvert, _, hcorrU⟩ :=
    T.exists_correlating_vertical_mode hp1 (hT.mono (by linarith)) (Real.exp_pos (-p))
      herror hQ f hf hcorr
  refine ⟨η, U, hU, ?_, hvert⟩
  apply le_trans _ hcorrU
  have hv := ha (p + 1) hp1
  calc
    _ ≤ Real.exp ((-p - verticalDecompositionBudget (p + 1)) - 1) := by
      apply Real.exp_le_exp.mpr
      unfold boxModeBudget
      linarith
    _ ≤ Real.exp (-p - verticalDecompositionBudget (p + 1)) / 2 := exp_sub_one_le_half_exp _
    _ = _ := by rw [Real.exp_sub]; ring

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def TranslatedStepDropSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {L : Type uL} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (_hvertical : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (origin : σ → ℤ) (lengths : σ → ℕ) (_hlengths : ∀ i, 0 < lengths i)
    (_hlarge : ∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ))
    (_hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖),
    D.filtration.ControlledSymbolFactorization D.basis ω _hF η (fun i => (lengths i : ℝ))
      (T.symbol D.basis ω _hF) ((p + C) ^ C)

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem stepOne_controlled_symbol_factorization (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z ∈ D.filtration.realification.subgroup 1, ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (origin : σ → ℤ) (lengths : σ → ℕ) (hlengths : ∀ i, 0 < lengths i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖) :
    D.filtration.ControlledSymbolFactorization D.basis ω hF η (fun i => (lengths i : ℝ))
      (T.symbol D.basis ω hF) ((p + 2) ^ 4) := by
  let U := T.translate (fun _ => Nat.zero_lt_one) origin
  have hUbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox lengths, U.eval x‖ := by
    rw [T.mean_translate_box (fun _ => Nat.zero_lt_one) origin lengths]
    exact hbias
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hheight, hη, hfast⟩ :=
    D.exists_stepOne_graded_niltest_splitting ω hF U η hp hT hηheight hvertical
      lengths hlengths hUbias
  refine ⟨m, E, P, R, W, v, hm, hmp, ?_, hE, hR, hv, hW, hheight, ?_, ?_⟩
  · exact hprod.trans (T.symbol_translate D.basis ω hF (fun _ => Nat.zero_lt_one) origin)
  · intro x hx _
    change D.filtration.stepOneGradedFrequency D.basis ω hF η x = 0
    exact hη x hx
  · exact (D.filtration.mem_real_symbolPointwiseSubalgebra_iff_values D.basis ω hF
      (fun _ => 1) W P.coord).mpr hfast

end RationalFilteredNilmanifold

theorem translatedStepDropSpec_one : TranslatedStepDropSpec.{uσ, uL} 1 4 := by
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p hp _ T hT η hη hvertical origin lengths hlengths _ hbias
  have h := D.stepOne_controlled_symbol_factorization ω hF T η hp hT hη hvertical
    origin lengths hlengths hbias
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono D.filtration D.basis ω hF h
    (pow_le_pow_left₀ (by linarith) (by norm_num) 4)
    (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  (bs : Basis (Fin m) ℚ F.squareLieSubalgebra) (ω : Fin m → ℕ)
  (hls : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (F.squareLattice Γ))
  (hout : bchSubgroupCoordinates bs (F.squareLattice Γ) ⊆ denominatorGrid N)

local notation "Dq" => F.squareFiltration.topQuotientModel bs ω hls (F.squareLattice Γ) N hN hin hout

theorem exists_correlating_square_vertical_mode (hs : 1 ≤ s) (w : σ → ℕ)
    (ε : F.realification.Group) (η : L →ₗ[ℚ] ℚ)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x,
      u (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * u x)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (S : (Dq).Niltest w)
    (hOrbit : S.orbit = F.squareFiltration.nativeReducedPolynomialOrbit w r)
    (hObs : ∀ z : F.squareFiltration.realification.Group,
      S.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
        F.realSquareObservable Γ ε u (QuotientGroup.mk z))
    {p ρ : ℝ} (hp : 0 ≤ p) (hS : S.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {A : Finset (σ → ℤ)} (hA : A.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation A f S.eval‖) :
    ∃ (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
      (V : (Dq).Niltest w),
      V.ComplexityLE p ∧ V.orbit = F.squareFiltration.nativeReducedPolynomialOrbit w r ∧
      (∀ i, rationalLogHeight (ξ ((Dq).basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
        V.observable (z • x) =
          character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
      (∀ z : (Dq).RealGroup, z ∈ F.squareFiltration.quotientTop.realification.subgroup s →
        z ∈ (Dq).realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
      (∀ x : F.layer (s + 1), ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation A f V.eval‖ := by
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hpres, hCorr⟩ :=
    S.exists_correlating_vertical_mode_preserving_characters hp hS hρ hρp hA f hf hcorr
  have hne : ∃ x, V.observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, V.eval x = 0 := fun _ => hzero _
    have hc0 : finiteCorrelation A f V.eval = 0 := by simp [finiteCorrelation, heval]
    rw [hc0, norm_zero] at hCorr
    exact (not_le_of_gt (div_pos hρ (by positivity))) hCorr
  refine ⟨ξ, V, hV, hVO.trans hOrbit, hheight, hchar, hint, ?_, hCorr⟩
  exact F.descended_square_mode_frequency_restriction hs Γ ε η u hu
    S.observable V.observable hObs ξ hchar hne hpres

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uι uL

namespace RationalFilteredNilmanifold

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uι uL

namespace RationalFilteredNilmanifold

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

def HasNativeBiasedSquareInModel {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (A : Finset (σ → ℤ)) (h : σ → ℤ) (q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp q) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (ξ : (D.filtration.squareLieSubalgebra ⧸
            D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
          (V : Q.Niltest (fun _ : σ => 1)),
          V.orbit = D.filtration.squareFiltration.nativeReducedPolynomialOrbit (fun _ => 1) r ∧
          V.ComplexityLE q ∧
          (∀ i, rationalLogHeight (ξ (Q.basis i)) ≤ q) ∧
          (∀ z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
            V.observable (z • x) =
              character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
          (∀ z : Q.RealGroup, z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s →
            z ∈ Q.realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
          (∀ x : D.filtration.layer (s + 1),
            ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
              (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
          Real.exp (-q) ≤ ‖𝔼 x ∈ A, V.eval x‖

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
theorem HasNativeBiasedSquareInModel.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {A : Finset (σ → ℤ)} {h : σ → ℤ} {p q : ℝ}
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h p) (hpq : p ≤ q) :
    D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h q := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative,
    ξ, V, hOrbit, hV, hheight, hchar, hint, hrestriction, hbias⟩ := hdata
  exact ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)),
    r, hf, hsecond, hderivative, ξ, V, hOrbit,
    hV.mono hpq, (fun i => (hheight i).trans hpq), hchar, hint, hrestriction,
    (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem topQuotientModel_basis_layers (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) (j : ℕ) :
    (F.topQuotientModel b w hF Γ N hN hin hout).filtration.layer j =
      Submodule.span ℚ ((F.topQuotientModel b w hF Γ N hN hin hout).basis ''
        {i | j ≤ quotientFinWeight w {i | s + 1 ≤ w i} i}) :=
  F.quotientFinBasis_layers b w hF (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hF (s + 1)) j

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

def HasNativeFactoredSquareInModel (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (h : σ → ℤ) (p q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ ξ : (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ,
        (∀ i, rationalLogHeight (ξ ((Q).basis i)) ≤ p) ∧
        (∀ x : D.filtration.layer (s + 1),
          ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
            (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
        (Q).filtration.ControlledSymbolFactorization (Q).basis
          (quotientFinWeight v {i | s + 1 ≤ v i}) hQ ξ S
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) q

variable [DecidableEq σ]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem HasNativeBiasedSquareInModel.factorization {c : ℕ}
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {origin h : σ → ℤ} {lengths : σ → ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p) (hlengths : ∀ i, 0 < lengths i)
    (hlarge : ∀ i, Real.exp ((p + c) ^ c) ≤ (lengths i : ℝ))
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η
      (translatedIntegerBox origin lengths) h p) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h p ((p + c) ^ c) := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative,
    ξ, V, hOrbit, hV, hheight, hchar, _, hrestriction, hbias⟩ := hdata
  have hfactor := hI Q (quotientFinWeight v {i | s + 1 ≤ v i}) hQ p hp hσ V hV ξ hheight hchar
    origin lengths hlengths hlarge hbias
  have hsymbol : V.symbol (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ =
      D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r := by
    have he := congrArg (fun a : (Q).filtration.realification.PolynomialOrbit (fun _ : σ => 1) =>
      (Q).filtration.realPolynomialSymbolHom (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i})
        hQ (fun _ => 1) ⟨⟨a.log, a.property⟩⟩) hOrbit
    exact he.trans (D.filtration.squareFiltration.nativeReducedPolynomialOrbit_symbol
      (fun _ => 1) (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ r)
  rw [hsymbol] at hfactor
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

def HasFixedNativeSquareFactors (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (h : σ → ℤ) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ ξ : (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ,
        (∀ i, rationalLogHeight (ξ ((Q).basis i)) ≤ p) ∧
        (∀ x : D.filtration.layer (s + 1),
          ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
            (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
        (∀ x ∈ W, basisGradeProjection
            ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
            (quotientFinWeight v {i | s + 1 ≤ v i}) s x = x →
          (Q).filtration.gradedFrequency (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ ξ x = 0) ∧
        (Q).filtration.SymbolFactorizationIn (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ S
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) p l W

theorem HasNativeFactoredSquareInModel.exists_fixed {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) → (Q).filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
        (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ).repr
          (u i) j) ≤ p) ∧
      D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  obtain ⟨l, W, u, hl, hlp, hu, hW, hcoordinates, hη, hfixed⟩ :=
    ControlledSymbolFactorization.exists_in (Q).filtration (Q).basis
      (quotientFinWeight v {i | s + 1 ≤ v i}) hQ hfactor
  refine ⟨l, W, u, hl, hlp, hu, hW, hcoordinates, ?_⟩
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hη, hfixed⟩

theorem HasFixedNativeSquareFactors.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p q : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W)
    (hpq : p ≤ q) (hS : ∀ i, 0 < S i) :
    D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h q l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hη, hfixed⟩ := hdata
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)), r,
    hf, hsecond, hderivative, ξ, (fun i => (hheight i).trans hpq), hrestriction, hη, ?_⟩
  exact SymbolFactorizationIn.mono (Q).filtration (Q).basis
    (quotientFinWeight v {i | s + 1 ≤ v i}) hQ hfixed hpq hS

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

theorem exists_common_native_square_factors (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (H : Finset (σ → ℤ)) (hH : H.Nonempty)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i} : ℝ) ≤ p)
    (hdata : ∀ h ∈ H, D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) → (Q).filtration.AssociatedGraded)
      (H' : Finset (σ → ℤ)),
      H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * H.card ≤ (H'.card : ℝ) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
        (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ).repr
          (u i) j) ≤ p) ∧
      ∀ h ∈ H', D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W := by
  classical
  let J := Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i})
  let bG := (Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ
  obtain ⟨h₀, hh₀⟩ := hH
  have htags : ∀ h : σ → ℤ, ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : J → (Q).filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule bG (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight (bG.repr (u i) j) ≤ p) ∧
      (h ∈ H → D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W) := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨l, W, u, hl, hlp, hu, hW, hhgt, hfixed⟩ :=
        HasNativeFactoredSquareInModel.exists_fixed D bs v hls N hN hin hout (hdata h hh)
      exact ⟨l, W, u, hl, hlp, hu, hW, hhgt, fun _ => hfixed⟩
    · obtain ⟨l, W, u, hl, hlp, hu, hW, hhgt, _⟩ :=
        HasNativeFactoredSquareInModel.exists_fixed D bs v hls N hN hin hout (hdata h₀ hh₀)
      exact ⟨l, W, u, hl, hlp, hu, hW, hhgt, fun he => False.elim (hh he)⟩
  choose l W u hl hlp hu hW hhgt hfixed using htags
  have hdim : (Fintype.card J : ℝ) ≤ p := by simpa only [J, Fintype.card_fin] using hd
  obtain ⟨a₀, _, H', hsub, ha, hsame, hlarge⟩ :=
    exists_common_fast_subalgebra_and_denominator bG H ⟨h₀, hh₀⟩ W l
      (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) hp hd hdim
      (fun h _ => ⟨u h, hu h, hhgt h⟩) (fun h _ => ⟨hl h, hlp h⟩)
  refine ⟨l a₀, W a₀, u a₀, H', hsub, ⟨a₀, ha⟩, hlarge,
    hl a₀, hlp a₀, hu a₀, hW a₀, hhgt a₀, ?_⟩
  intro h hh
  simpa only [(hsame h hh).1, (hsame h hh).2] using hfixed h (hsub hh)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


