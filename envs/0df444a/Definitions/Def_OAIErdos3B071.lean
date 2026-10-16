-- Prove2me | Definitions.Def_OAIErdos3B071
-- name    : OAIErdos3B071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T17:23:13.278867+00:00
-- url     : https://prove2.me/theorems/78ac2b80-fa6a-4061-bac7-da24d884e95b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 72 of 1328
-- statement:
--   Definitions bundle 72 of 1328 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B070`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 72 available.
--
--   Modules: `OAI.Erdos3.NativeCorrelationStructure.HasLocalInducedFamily`, `OAI.Erdos3.NativeCorrelationStructure.HasLocalMarkedFamily`, `OAI.Erdos3.NativeCorrelationStructure.absorbRankZero`, `OAI.Erdos3.NativeDegreeRankDerivativeData.toCorrelationStructure`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicDiagonalDerivative_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicDiagonalDerivative_unit`, `OAI.Erdos3.NativeMultidegreeNilcharacter.original_diagonal_row_correlation_bound`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixed_pair_top_agreement`, `OAI.Erdos3.NativeRankRelation.CommonData.CorrelatedAffineComparison.localMarkedFamily`, `OAI.Erdos3.NativeRankRelation.CommonData.CorrelatedLocalInducedFamily`, `OAI.Erdos3.NativeRankRelation.CommonData.CorrelatedLocalInducedFamily.product`, `OAI.Erdos3.NativeRankRelation.CommonData.CorrelatedLocalMarkedFamily`, `OAI.Erdos3.NativeRankRelation.CommonData.CorrelatedLocalMarkedFamily.induce`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairComparison_component_cost`, `OAI.Erdos3.RationalFilteredNilmanifold.HasLowerRankOrbitFamily.reindex`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_residual_row_differences_degree`, `OAI.Erdos3.dense_set_mean_lower_bound`, `OAI.Erdos3.exists_initial_native_correlation_structure`, `OAI.Erdos3.exists_localCoveredInducedBudget_bound`, `OAI.Erdos3.exists_mixed_pair_orbit_factors`, `OAI.Erdos3.exists_mixed_pair_outer_control`, `OAI.Erdos3.exists_native_common_factor_products`, `OAI.Erdos3.exists_native_local_induced_family`, `OAI.Erdos3.exists_native_local_marked_family`, `OAI.Erdos3.exists_native_product_correlation`, `OAI.Erdos3.exists_native_rank_descent`, `OAI.Erdos3.exists_native_rank_zero_reduction`, `OAI.Erdos3.exists_quadratic_pair_orbit_factors`, `OAI.Erdos3.exists_retained_inverse_intervals`, `OAI.Erdos3.exists_unit_row_family_with_differences`, `OAI.Erdos3.exists_unit_row_model_with_differences`, `OAI.Erdos3.exists_weighted_common_factor`, `OAI.Erdos3.localCoveredInducedBudget`, `OAI.Erdos3.norm_mul_star_sub_mul_star_le_of_le_one`, `OAI.Erdos3.productNiltestBudget_mono`, `OAI.Erdos3.quadratic_original_error_bound`, `OAI.Erdos3.unit_row_correlation_bound`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B196
import Definitions.Def_OAIErdos3B209

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_weighted_common_factor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} {I J K : Type*}
      [Fintype σ] [Fintype I] [Fintype K] {s N : ℕ} [NeZero N] {p : ℝ},
      2 ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ (w : I → σ → ZMod N → ℝ) (v : I → J → (σ → ℤ) → ℂ)
        (u : K → (σ → ℤ) → ℂ),
        (∀ i a, PositiveCyclicNiltest.{0} s N p (w i a)) →
        (∀ x : σ → ZMod N, ∑ i, ∏ a, w i a (x a) = 1) →
        (∀ i j (x : σ → ZMod N), ‖v i j (fun a => ((x a).val : ℤ))‖ ≤ 1) →
        (∀ k (x : σ → ZMod N), ‖u k (fun a => ((x a).val : ℤ))‖ ≤ 1) →
        (∀ x : σ → ZMod N, ∑ k, ‖u k (fun a => ((x a).val : ℤ))‖ ^ 2 = 1) →
        (∀ i j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
          (fun x => v i j x * star (u k x)))) →
        ∃ F : J → K → (σ → ℤ) → ℂ,
          (∀ j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j k))) ∧
          (∀ j k (x : σ → ZMod N), F j k (fun a => ((x a).val : ℤ)) =
            (∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) *
              star (u k (fun a => ((x a).val : ℤ)))) ∧
          (∀ j k (x : σ → ZMod N), ‖F j k (fun a => ((x a).val : ℤ))‖ ≤ 1) ∧
          (∀ j (x : σ → ZMod N),
            ∑ k, F j k (fun a => ((x a).val : ℤ)) * u k (fun a => ((x a).val : ℤ)) =
            ∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  obtain ⟨B, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let R := (Y + Polynomial.C B) ^ B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro σ I J K _ _ _ s N _ p hp hσ hI w v u hw htotal hv hu hunit hexp
  classical
  have hp0 : 0 ≤ p := by linarith
  have hy : 0 ≤ raisedNiltestBudget p := hp0.trans (le_raisedNiltestBudget p)
  let r := (raisedNiltestBudget p + B) ^ B + p + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ raisedNiltestBudget p + B) B]
  have hwr : productNiltestBudget (raisedNiltestBudget p) ≤ r :=
    (hproduct _ hy).trans (by dsimp [r]; linarith)
  have hcost : (r + A) ^ A + p ≤ (p + C) ^ C := by
    simpa [X, Y, R, r, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hweights (i : I) := exists_positive_coordinate_product hp0 hσ (hw i)
  choose g hgExpansion hg using hweights
  have hproducts (i : I) (j : J) (k : K) :
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((r + A) ^ A)
        (fun x => g i x * (v i j x * star (u k x)))) :=
    hmul hr ((Classical.choice (hgExpansion i)).mono hwr)
      ((Classical.choice (hexp i j k)).mono hpr)
  let E (i : I) (j : J) (k : K) := Classical.choice (hproducts i j k)
  let F (j : J) (k : K) (x : σ → ℤ) := ∑ i, g i x * (v i j x * star (u k x))
  have hF (j : J) (k : K) :
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j k)) := by
    have hc : (∑ _ : I, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hI
    have H := (NativeIntegerExpansion.weightedSum (fun i => E i j k)
      (fun _ => (1 : ℂ)) hp0 hI hc).mono hcost
    exact ⟨by simpa only [one_mul] using H⟩
  have heq (j : J) (k : K) (x : σ → ZMod N) : F j k (fun a => ((x a).val : ℤ)) =
      (∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) *
        star (u k (fun a => ((x a).val : ℤ))) := by
    simp only [F, hg, Complex.ofReal_prod, Finset.sum_mul, mul_assoc]
  refine ⟨F, hF, heq, ?_, ?_⟩
  · intro j k x
    rw [heq, norm_mul, norm_star]
    have hsum : ‖∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) *
        v i j (fun a => ((x a).val : ℤ))‖ ≤ 1 :=
      norm_positive_partition_sum_le_one (fun i => ∏ a, w i a (x a))
        (fun i => v i j (fun a => ((x a).val : ℤ)))
        (fun i => Finset.prod_nonneg (fun a _ => ((hw i a).unit_interval (x a)).1))
        (htotal x) (fun i => hv i j x)
    exact (mul_le_of_le_one_left (norm_nonneg _) hsum).trans (hu k x)
  · intro j x
    simp_rw [heq]
    exact (complex_unit_vector_resolution (fun k => u k (fun a => ((x a).val : ℤ)))
      (hunit x) _).symm

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

end Data

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r}

namespace NativePolynomialOrbitFactors

end NativePolynomialOrbitFactors

end Data

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

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

variable
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

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_common_factor_products :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K : Type*} [Fintype K] {w : σ → ℕ} {s : ℕ} {p : ℝ},
      0 ≤ p → (Fintype.card K : ℝ) ≤ Real.exp p →
      ∀ (F : J → K → (σ → ℤ) → ℂ) (U : K → (σ → ℤ) → ℂ),
        (∀ j k, Nonempty (NativeIntegerExpansion w s p (F j k))) →
        (∀ a b, Nonempty (NativeIntegerExpansion w s p
          (fun x => U a x * star (U b x)))) →
        ∀ i j, Nonempty (NativeIntegerExpansion w s ((p + C) ^ C)
          (fun x => (∑ a, F i a x * U a x) * star (∑ b, F j b x * U b x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K _ w s p hp hK F U hF hU i j
  classical
  let r := p + (p + A) ^ A + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by
    have : 0 ≤ (p + A) ^ A := by positivity
    dsimp [r]
    linarith
  have har : (p + A) ^ A ≤ r := by dsimp [r]; linarith
  have hcost : (r + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hterm (a b : K) : Nonempty (NativeIntegerExpansion w s ((r + A) ^ A)
      (fun x => (F i a x * star (F j b x)) * (U a x * star (U b x)))) := by
    obtain ⟨E⟩ := hmul hp (Classical.choice (hF i a)) (Classical.choice (hF j b)).conjugate
    exact hmul hr (E.mono har) ((Classical.choice (hU a b)).mono hpr)
  have hcount : (Fintype.card (K × K) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul, two_mul, Real.exp_add]
    exact mul_le_mul hK hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hcoeff : (∑ _ : K × K, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcount
  let E := (NativeIntegerExpansion.weightedSum
    (fun ab : K × K => Classical.choice (hterm ab.1 ab.2)) (fun _ => (1 : ℂ))
    (by positivity : 0 ≤ 2 * p) hcount hcoeff).mono hcost
  have heq : (fun x => ∑ ab : K × K,
      (1 : ℂ) * ((F i ab.1 x * star (F j ab.2 x)) * (U ab.1 x * star (U ab.2 x)))) =
      (fun x => (∑ a, F i a x * U a x) * star (∑ b, F j b x * U b x)) := by
    funext x
    simp only [one_mul, Fintype.sum_prod_type, star_sum, star_mul]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  exact ⟨heq ▸ E⟩

theorem norm_mul_star_sub_mul_star_le_of_le_one {a b c d : ℂ}
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * star b - c * star d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  calc
    _ = ‖(a - c) * star b + c * star (b - d)‖ := by
      congr 1
      simp only [star_sub]
      ring
    _ ≤ ‖(a - c) * star b‖ + ‖c * star (b - d)‖ := norm_add_le _ _
    _ = ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by simp only [norm_mul, norm_star]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) hb)
      (mul_le_of_le_one_left (norm_nonneg _) hc)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quadratic_pair_orbit_factors :
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
                  Nonempty (NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
                    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
                    (fun _ : Fin 2 => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨A, _, hdrop⟩ := exists_quadratic_pair_step_drop
  obtain ⟨B, _, horbit⟩ := exists_antisymmetric_pair_orbit_factors
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (3 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (3 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨F⟩⟩ :=
    hdrop hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hbound : (q + r + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + r + t + B ≤ 3 * t + B
    linarith
  obtain ⟨R⟩ := horbit F ht ((Real.exp_le_exp.mpr hbound).trans hN)
  exact ⟨q, r, hq, hqt.trans htC, hr, hrt.trans htC, H, hH, hdense, M, i, hderiv, i', j', V,
    ⟨R.mono hbound (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem quadratic_original_error_bound {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + 4 * u + 40) ≤ N) :
    d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40))))) +
        12 * Real.exp (-(e + 4 * u + 40)) + 2 / N) ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have h2 : d ^ 2 + 1 ≤ 2 * Real.exp (2 * u) := by
    have hh := hp 2
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.one_le_exp (show 0 ≤ 2 * u by positivity)]
  have hplus : (d ^ 2 + 1) ^ 2 ≤ 4 * Real.exp (4 * u) := by
    calc
      _ ≤ (2 * Real.exp (2 * u)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = 4 * Real.exp (4 * u) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
        ring_nf
  have hcoef : 4 * d ^ 8 * (d ^ 2 + 1) ^ 2 ≤ 16 * Real.exp (12 * u) := by
    calc
      _ ≤ 4 * Real.exp (8 * u) * (4 * Real.exp (4 * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using hp 8)
          (by norm_num)) hplus (by positivity) (by positivity)
      _ = _ := by rw [show 4 * Real.exp (8 * u) * (4 * Real.exp (4 * u)) =
        16 * (Real.exp (8 * u) * Real.exp (4 * u)) by ring, ← Real.exp_add]; congr 2; ring
  have hfirst : d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40)))))) ≤ 16 * Real.exp (-(e + 40)) := by
    calc
      _ = (4 * d ^ 8 * (d ^ 2 + 1) ^ 2) * Real.exp (-(e + 12 * u + 40)) := by ring
      _ ≤ (16 * Real.exp (12 * u)) * Real.exp (-(e + 12 * u + 40)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hfour : d ^ 4 ≤ Real.exp (4 * u) := by simpa only [Nat.cast_ofNat] using hp 4
  have hscaled : d ^ 4 * Real.exp (-(e + 4 * u + 40)) ≤ Real.exp (-(e + 40)) := by
    calc
      _ ≤ Real.exp (4 * u) * Real.exp (-(e + 4 * u + 40)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + 4 * u + 40)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have hthird : d ^ 4 * (2 / N) ≤ 2 * Real.exp (-(e + 40)) := by
    have hh := (mul_le_mul_of_nonneg_left hrecip (pow_nonneg hd 4)).trans hscaled
    calc
      _ = 2 * (d ^ 4 * (1 / N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  have hsum : d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40))))) +
        12 * Real.exp (-(e + 4 * u + 40)) + 2 / N) ≤ 30 * Real.exp (-(e + 40)) := by
    nlinarith
  apply hsum.trans
  calc
    _ ≤ Real.exp 40 * Real.exp (-(e + 40)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (40 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem unit_row_correlation_bound {H X I J : Type*}
    [Fintype H] [Fintype X] [Fintype I] [Fintype J]
    (f q : H → X → ℂ) (u : I → H → X → ℂ) (v : J → H → ℂ)
    (K : I → J → H → X → ℂ)
    (hf : ∀ h x, ‖f h x‖ ≤ 1)
    (hu : ∀ h x, ∑ i, ‖u i h x‖ ^ 2 = 1) (hv : ∀ h, ∑ j, ‖v j h‖ ^ 2 = 1)
    (huc : ∀ i h x, ‖u i h x‖ ≤ 1) (hvc : ∀ j h, ‖v j h‖ ≤ 1)
    {ε : ℝ} (herr : ∀ i j, (𝔼 h, 𝔼 x, ‖q h x * (u i h x * v j h) - K i j h x‖) ≤ ε) :
    (𝔼 h, ‖𝔼 x, f h x * star (q h x)‖) ≤
      (∑ ij : I × J, 𝔼 h, ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖) +
        Fintype.card (I × J) * ε := by
  let z (ij : I × J) (h : H) (x : X) := u ij.1 h x * v ij.2 h
  have hz (h : H) (x : X) : ∑ ij : I × J, ‖z ij h x‖ ^ 2 = 1 := by
    simp only [z, Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, hv, mul_one, hu]
  have hzc (ij : I × J) (h : H) (x : X) : ‖z ij h x‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (huc _ _ _)).trans (hvc _ _)
  let t (ij : I × J) (h : H) (x : X) := star (z ij h x) * K ij.1 ij.2 h x
  have he (h : H) (x : X) : ‖q h x - ∑ ij, t ij h x‖ ≤
      ∑ ij : I × J, ‖q h x * z ij h x - K ij.1 ij.2 h x‖ := by
    have hh := norm_unit_vector_exchange_error (fun ij => star (z ij h x))
      (by simpa only [norm_star] using hz h x)
      (fun ij => by simpa only [norm_star] using hzc ij h x)
      (q h x) (fun ij => star (K ij.1 ij.2 h x))
    simpa only [t, star_star, ← star_mul, ← star_sub, norm_star, mul_comm] using hh
  have hterm (ij : I × J) (h : H) :
      ‖𝔼 x, f h x * star (t ij h x)‖ ≤ ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖ := by
    have heq : (𝔼 x, f h x * star (t ij h x)) =
        v ij.2 h * (𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [t, z, star_mul, star_star]
      ring
    rw [heq, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hvc _ _)
  have hp (h : H) : ‖𝔼 x, f h x * star (q h x)‖ ≤
      (∑ ij : I × J, ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖) +
        (𝔼 x, ∑ ij : I × J, ‖q h x * z ij h x - K ij.1 ij.2 h x‖) := by
    apply (norm_correlation_partition_bound (f h) (q h) (fun ij => t ij h) (hf h)).trans
    exact add_le_add (Finset.sum_le_sum (fun ij _ => hterm ij h))
      (Finset.expect_le_expect (fun x _ => he h x))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hp h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm] at hm
  apply hm.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _ij : I × J, ε := Finset.sum_le_sum (fun ij _ => herr ij.1 ij.2)
    _ = _ := by simp

namespace NativeMultidegreeNilcharacter

theorem cyclicDiagonalDerivative_unit {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.cyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [cyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem cyclicDiagonalDerivative_norm {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [cyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem original_diagonal_row_correlation_bound {p ε : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim)
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (K : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      Fin W.quadraticRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
        (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
        K a c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (W.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ ac : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) × Fin W.quadraticRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
          W.quadraticRoot.cyclicDiagonalDerivative ac.1 ![h, n] *
            star (K ac.1 ac.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
        (W.quadraticRoot.outputDim : ℝ) ^ 3 * ε := by
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : W.evalCyclic N i (correlationInput h n) = W.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hh := unit_row_correlation_bound (multiplicativeDerivative f)
    (fun h n => W.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun a h n => W.quadraticRoot.cyclicDiagonalDerivative a ![h, n])
    (fun c h => W.quadraticRoot.eval c (fun _ => (h.val : ℤ)))
    (fun a c h n => K a c ![(h.val : ℤ), (n.val : ℤ)])
    (fun h => multiplicativeDerivative_norm_le_one f hf h)
    (fun h n => W.quadraticRoot.cyclicDiagonalDerivative_unit ![h, n])
    (fun h => W.quadraticRoot.unit_eval _) (fun a h n => W.quadraticRoot.cyclicDiagonalDerivative_norm a ![h, n])
    (fun c h => W.quadraticRoot.norm_eval _ _) (ε := ε) (by
      intro a c
      have he := herr a c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hc : (Fintype.card ((Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) × Fin W.quadraticRoot.outputDim) : ℝ) =
      (W.quadraticRoot.outputDim : ℝ) ^ 3 := by simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]; ring
  simpa only [heval, hc] using hh

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem HasLowerRankOrbitFamily.reindex {L I σ τ τ' : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {w : σ → ℕ} {f : τ → I → (σ → ℤ) → ℂ} {p : ℝ}
    (h : D.HasLowerRankOrbitFamily R w f p) (j : τ' → τ) :
    D.HasLowerRankOrbitFamily R w (fun t => f (j t)) p := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, ha⟩ := hK
  exact ⟨K, hKn, hKc, hKu, (fun t => a (j t)),
    (fun t => ha0 (j t)), fun t i x => ha (j t) i x⟩

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedLocalMarkedFamily (hs : 2 ≤ s) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      ∃ t : ℕ, (t : ℝ) ≤ Λ ∧ ∃ (h₀ : ZMod N) (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∃ A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          (∀ h : {h // h ∈ J},
            (∀ i, |affineCyclicTorusLocalLift u c h₀ h.val i| ≤ 1 / 16) ∧
            (A h).log = positiveUnivariate (fun j => (x j).val +
              ∑ i, affineCyclicTorusLocalLift u c h₀ h.val i • (y j i).val) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            (∀ j : Fin s,
              coefficients (K h).log (Finsupp.single () (j.val + 1)) ∈
                (T.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (j.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan j)
                  (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
                    (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩))).baseChange ℝ) ∧
            ∀ n : ℤ,
              (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t
                  (fun i => (-affineCyclicTorusCarry u c h₀ h.val i : ℤ))).baseChange ℝ
                    (D.localAffineMarkedLift t x y u c h₀ h.val n) =
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => n) (A h)).coord) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc)

theorem CorrelatedAffineComparison.localMarkedFamily
    (hs : 2 ≤ s) (hP' : 0 ≤ P')
    (hdense : Real.exp (-P') * N ≤ (H'.card : ℝ))
    (h : D.CorrelatedAffineComparison E T hbQ hT V g hg D' hs) :
    D.CorrelatedLocalMarkedFamily E T hbQ hT V g hg D' hs := by
  classical
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let C := sharedFreeCorrelationBudget s hs P'
  let B := P' + Λ + C
  obtain ⟨J, hJH, hJ, hJcard, t, radius, η, h₀, Γ, α, β,
    ht, hinj, hΓ0, hΓ, hα, hβ, v, A, K, U, hdata,
    Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hfreq, hcorr, M, Tm, hTm, hTmc, hfamily⟩ := h
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hP' (Nat.cast_nonneg _)) _
  have hC : 0 ≤ C :=
    (show 0 ≤ sharedFreeCorrelationInput s P' by
      linarith only [(sharedFreeCorrelationInput_bounds s hP' le_rfl hP').1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hP')
  have hB : 0 ≤ B := add_nonneg (add_nonneg hP' hΛ) hC
  have htB : (t : ℝ) ≤ B := ht.trans (by dsimp only [B]; linarith only [hP', hC])
  have hJB : Real.exp (-B) * N ≤ (J.card : ℝ) := by
    calc
      _ = Real.exp (-(Λ + C)) * (Real.exp (-P') * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [B]
        ring
      _ ≤ Real.exp (-(Λ + C)) * H'.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_pos _).le
      _ ≤ _ := hJcard
  let v' (h : ZMod N) := if hh : h ∈ J then v ⟨h, hh⟩ else 0
  let A' (h : ZMod N) := if hh : h ∈ J then (A ⟨h, hh⟩).log else 0
  have hv' (h : ZMod N) (hh : h ∈ J) : ∀ i, |v' h i| ≤ (radius i : ℤ) := by
    simpa only [v', dif_pos hh] using (hdata ⟨h, hh⟩).1
  have hrep' (h : ZMod N) (hh : h ∈ J) : h = h₀ + η (v' h) := by
    simpa only [v', dif_pos hh] using (hdata ⟨h, hh⟩).2.1
  have hA' (h : ZMod N) (hh : h ∈ J) :
      A' h = Γ.log + positiveUnivariate (fun j => α j + ∑ i, (v' h i : ℝ) • β i j) := by
    simpa only [A', v', dif_pos hh] using (hdata ⟨h, hh⟩).2.2.1
  have hΓzero : coefficients Γ.log 0 = 0 := by
    have he := congrArg NilpotentLieBCHGroup.coord hΓ0
    simpa only [E.filtration.realification.polynomialOrbitEval_coord, Pi.zero_apply,
      Int.cast_zero, eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using he
  have hΓmem (j : Fin s) : coefficients Γ.log (Finsupp.single () (j.val + 1)) ∈
      (D.coefficientFreeSpan j).baseChange ℝ :=
    Submodule.baseChange_mono ℝ
      (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan j) _) (hΓ j)
  obtain ⟨J₁, hJ₁J, hJ₁, hcard, u, c, x, y, hu, hperiod, hc, hlocal⟩ :=
    D.exists_common_local_marked_family hB htB η radius hinj h₀ J hJ hJB v' hv' hrep'
      A' Γ.log Γ.degreeLE hΓzero hΓmem α β (fun j => (hα j).1) (fun i j => (hβ i j).1) hA'
  let lift (h : {h // h ∈ J₁}) : {h // h ∈ J} := ⟨h.val, hJ₁J h.property⟩
  refine ⟨J₁, (fun h hh => hJH (hJ₁J hh)), hJ₁, hcard, t, ht,
    h₀, u, c, x, y, hu, hperiod, hc, (fun h => A (lift h)), (fun h => K (lift h)),
    (fun h => U (lift h)), ?_, Δ, hΔ, hchar, hnormal, hfinite, hindex,
    l, hl, hin, hout, hRank, V₁, hfreq, (fun h => hcorr (lift h)), M, Tm, hTm, hTmc, ?_⟩
  · intro h
    obtain ⟨hsmall, hpoly, heval⟩ := hlocal h.val h.property
    have hAA : A' h.val = (A (lift h)).log := by simp only [A', dif_pos (hJ₁J h.property), lift]
    rw [hAA] at hpoly heval
    obtain ⟨_, _, _, hA0, hK0, hU0, hKU⟩ := hdata (lift h)
    refine ⟨hsmall, hpoly, hA0, hK0, hU0, hKU, ?_⟩
    intro n
    exact heval n
  · exact hfamily.reindex lift

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def localCoveredInducedBudget (s : ℕ) (hs : 2 ≤ s) (q p : ℝ) : ℝ :=
  let Z := q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
    sharedFreeCorrelationBudget s hs p + 2
  let C := (NativeRankRelation.CommonData.exists_covered_induced_correlation_family s (by omega)).choose
  (Z + C) ^ C

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedLocalInducedFamily (hs : 2 ≤ s) (Bound : ℝ) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      ∃ t : ℕ, (t : ℝ) ≤ Λ ∧ ∃ (h₀ : ZMod N) (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∃ A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          (∀ h : {h // h ∈ J},
            (∀ i, |affineCyclicTorusLocalLift u c h₀ h.val i| ≤ 1 / 16) ∧
            (A h).log = positiveUnivariate (fun j => (x j).val +
              ∑ i, affineCyclicTorusLocalLift u c h₀ h.val i • (y j i).val) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            (∀ j : Fin s,
              coefficients (K h).log (Finsupp.single () (j.val + 1)) ∈
                (T.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (j.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan j)
                  (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
                    (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩))).baseChange ℝ) ∧
            ∀ n : ℤ,
              (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t
                  (fun i => (-affineCyclicTorusCarry u c h₀ h.val i : ℤ))).baseChange ℝ
                    (D.localAffineMarkedLift t x y u c h₀ h.val n) =
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => n) (A h)).coord) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                (∃ hCZ : C ≤ Q + Λ + C + 2,
                  D.HasCoveredInducedCorrelationFamily (degree := s - 1)
                    t (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout)
                    (V₁.mono hCZ) x y u c h₀ (fun h : {h // h ∈ J} => h.val)
                    A (fun h => A h * K h * U h)
                    (fun h i z => multiplicativeDerivative f h.val z *
                      star (W.mixed.evalCyclic N i (correlationInput h.val z))) Bound) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc)

theorem CorrelatedLocalMarkedFamily.induce
    (B₀ : D.CoefficientBases Q) (F : FreeCoordinateFrame E.basis Q)
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P')
    (hlocal : D.CorrelatedLocalMarkedFamily E T hbQ hT V g hg D' hs) :
    let Z := Q + (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs P' + 2
    let C := (exists_covered_induced_correlation_family s (by omega)).choose
    D.CorrelatedLocalInducedFamily E T hbQ hT V g hg D' hs ((Z + C) ^ C) := by
  intro Z Cout
  obtain ⟨J, hJH, hJ, hJcard, t, ht, h₀, u, c, x, y, hu, hperiod, hc,
    A, K, U, hdata, Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hVfreq, hcorr, M, Tm, hTm, hTmc, hfamily⟩ := hlocal
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let Cc := sharedFreeCorrelationBudget s hs P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg W.family.dim).trans (W.family.complexity.1.1.trans hbQ)
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have hCc : 0 ≤ Cc :=
    (show 0 ≤ sharedFreeCorrelationInput s P' by
      linarith only [(sharedFreeCorrelationInput_bounds s hP' le_rfl hP').1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hP')
  have hCZ : Cc ≤ Z := by
    change Cc ≤ Q + Λ + Cc + 2
    linarith
  have hQZ : Q ≤ Z := by
    change Q ≤ Q + Λ + Cc + 2
    linarith
  have hΛZ : Λ ≤ Z := by
    change Λ ≤ Q + Λ + Cc + 2
    linarith
  have hZ : 0 ≤ Z := hCc.trans hCZ
  refine ⟨J, hJH, hJ, hJcard, t, ht, h₀, u, c, x, y, hu, hperiod, hc,
    A, K, U, hdata, Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hVfreq, hcorr, ?_, M, Tm, hTm, hTmc, hfamily⟩
  refine ⟨hCZ, ?_⟩
  apply (exists_covered_induced_correlation_family s (by omega)).choose_spec.2
    D B₀ t (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout) (V₁.mono hCZ)
    hTfil (hVfreq.trans hfreq) hZ (hRank.mono _ hCZ) (ht.trans hΛZ)
    (fun i j => (F.generator_height (by omega) i j).trans hQZ)
    (by
      simpa only [Fintype.card_fin] using
        W.family.output_bound.trans (Real.exp_le_exp.mpr (hbQ.trans hQZ)))
    x y u c h₀ (fun h : {h // h ∈ J} => h.val) A (fun h => A h * K h * U h)
    (fun h i => ((hdata h).1 i).trans (by norm_num))
    (fun h => (hdata h).2.1) (fun h => (hdata h).2.2.1)
  intro h
  exact (hcorr h).map (fun B => B.mono hCZ)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def NativeCorrelationStructure.HasLocalMarkedFamily
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedLocalMarkedFamily E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs ∧
                  (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

theorem exists_native_local_marked_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasLocalMarkedFamily hs C := by
  obtain ⟨a, _, hsource⟩ := exists_native_correlated_affine_comparison s hs
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (A₀ + (A₀ + 4) ^ 7)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg _).trans W.family.complexity.1.1
  have hsum : (p + a) ^ a + ((p + a) ^ a + 4) ^ 7 ≤ (p + C) ^ C := by
    simpa [A₀, Polynomial.eval₂_pow] using hbound p hp
  have ha0 : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hchart : ((p + a) ^ a + 4) ^ 7 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left ha0).trans hsum
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
      R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr haC).trans hN)
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q',
      hsub, hH', hshort', hdense, hAq', hq'Z, R', D', hcomp, htotal, hpair, hlower⟩ := hdata
  have hdense' : Real.exp (-Z) * N ≤ (H'.card : ℝ) := by
    simpa only [ZMod.card] using hdense
  have hlocal := hcomp.localMarkedFamily D E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs hZ hdense'
  have htotal0 : 0 ≤ Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z := by
    have hcorr0 : 0 ≤ sharedFreeCorrelationBudget s hs Z :=
      (show 0 ≤ sharedFreeCorrelationInput s Z by
        linarith only [(sharedFreeCorrelationInput_bounds s hZ le_rfl hZ).1]).trans
          (sharedFreeCorrelationInput_le_budget s hs hZ)
    exact add_nonneg (add_nonneg hZ (pow_nonneg (add_nonneg hZ (Nat.cast_nonneg _)) _)) hcorr0
  have htotalC : (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C :=
    (pow_le_pow_left₀ (add_nonneg htotal0 (by norm_num))
      (add_le_add htotal (le_rfl : (4 : ℝ) ≤ 4)) 7).trans hchart
  exact ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z,
    R', D', hlocal, htotalC, hpair.trans haC, hlower.trans haC⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CorrelatedLocalInducedFamily.product (hs : 2 ≤ s) {Bound : ℝ}
    (hlocal : D.CorrelatedLocalInducedFamily E T hbQ hT V g hg D' hs Bound) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    0 ≤ Bound ∧ 0 ≤ nativeLowerPairModelBudget s Qc ∧
    ∃ J : Finset (ZMod N), J ⊆ H' ∧ J.Nonempty ∧
      Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      HasBoundedProductCorrelation (I := Fin W.family.outputDim) (s := s) (r := r) (degree := s - 1)
        (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
        W.mixed.outputDim Bound
        (productNiltestBudget (nativeLowerPairModelBudget s Qc + Bound + 2))
        (productNiltestBudget (b + Bound + 2 + 4)) := by
  intro Λ C B Qc
  obtain ⟨J, hJH, hJ, hJcard, t, _, h₀, u, c, x, y, _, _, _,
    A, K, U, _, Δ, _, _, _, _, _, l, hl, hin, hout,
    _, V₁, _, _, hcovered, M, Tm, _, _, hfirst⟩ := hlocal
  obtain ⟨hCZ, hcovered⟩ := hcovered
  have hBound : 0 ≤ Bound := by
    obtain ⟨Δ₂, _, l₂, hl₂, hin₂, hout₂, hT₂, _⟩ := hcovered
    exact (Nat.cast_nonneg _).trans hT₂.1.1
  have hFirst : 0 ≤ nativeLowerPairModelBudget s Qc := by
    obtain ⟨n₀, _, Q₀, R₀, hR₀, _⟩ := hfirst
    exact (Nat.cast_nonneg n₀).trans hR₀.1.1
  have hunit := HasCoveredInducedCorrelationFamily.combineLower
    D t x y u c h₀ (fun h : {h // h ∈ J} => h.val)
    (fun h i z => multiplicativeDerivative f h.val z *
      star (W.mixed.evalCyclic N i (correlationInput h.val z)))
    (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout)
    (V₁.mono hCZ) A (fun h => A h * K h * U h)
    hBound hFirst hcovered M Tm hfirst
  refine ⟨hBound, hFirst, J, hJH, hJ, hJcard, ?_⟩
  exact HasUnitRankInducedCorrelationFamily.combineMixed D t x y u c h₀
    (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
    W.mixed hBound hunit

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_localCoveredInducedBudget_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      localCoveredInducedBudget s hs q p ≤ (p + C) ^ C := by
  obtain ⟨a, _, hsource⟩ := exists_sharedFreeCorrelationBudget_bound s hs
  let c := (NativeRankRelation.CommonData.exists_covered_induced_correlation_family s (by omega)).choose
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a +
    2 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  obtain ⟨hsize, _, _⟩ := hsource q p hq hqp hp
  have hcorr : 0 ≤ sharedFreeCorrelationBudget s hs p :=
    (show 0 ≤ sharedFreeCorrelationInput s p by
      linarith only [(sharedFreeCorrelationInput_bounds s hp le_rfl hp).1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hp)
  have hbase : 0 ≤ q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs p + 2 + c := by positivity
  have hle : q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs p + 2 + c ≤ p + (p + a) ^ a + 2 + c := by linarith
  have hb : (p + (p + a) ^ a + 2 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact (pow_le_pow_left₀ hbase hle c).trans hb

def NativeCorrelationStructure.HasLocalInducedFamily
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedLocalInducedFamily E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs
                    (localCoveredInducedBudget s hs A Z) ∧
                  localCoveredInducedBudget s hs A Z ≤ (p + C) ^ C ∧
                  (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

theorem exists_native_local_induced_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasLocalInducedFamily hs C := by
  obtain ⟨a, _, hsource⟩ := exists_native_local_marked_family s hs
  obtain ⟨b, _, hlocalBudget⟩ := exists_localCoveredInducedBudget_bound s hs
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Z₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C (nativeSharedFreeRelationConstant s hs)) ^
    nativeSharedFreeRelationConstant s hs
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (Z₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have htotal : (p + a) ^ a + (Z + b) ^ b ≤ (p + C) ^ C := by
    simpa [A₀, Z₀, Z, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hbC : (Z + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left (by positivity)).trans htotal
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr haC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q', hsub, hH',
    hshort', hdense, hAq', hq'Z, R', D', hlocal, hchart, hpair, hlower⟩ := hdata
  obtain ⟨F⟩ := hframe
  have hinduced := hlocal.induce D E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' B F hTfil hfreq hs hZ
  have hbound : localCoveredInducedBudget s hs A Z ≤ (p + C) ^ C :=
    (hlocalBudget A Z (hp.trans hpA) hAZ hZ).trans hbC
  refine ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, ⟨F⟩, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z, R', D',
    hinduced, hbound, hchart.trans haC, hpair.trans haC, hlower.trans haC⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem productNiltestBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    productNiltestBudget p ≤ productNiltestBudget q := by
  unfold productNiltestBudget productObservableLipBudget
  gcongr

theorem exists_native_product_correlation (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∃ J : Finset (ZMod N), J ⊆ W.shifts ∧ J.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (J.card : ℝ) ∧
        HasBoundedProductCorrelation (I := Fin W.family.outputDim) (s := s) (r := r) (degree := s - 1)
          (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
          W.mixed.outputDim ((p + C) ^ C) ((p + C) ^ C) ((p + C) ^ C) := by
  obtain ⟨a, _, hsource⟩ := exists_native_local_induced_family s hs
  let X : Polynomial ℕ := Polynomial.X
  let R₀ : Polynomial ℕ := (X + Polynomial.C a) ^ a
  let P₀ : Polynomial ℕ := X + 2 * R₀ + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (R₀ + ((P₀ + 2) ^ 2 + P₀ + (P₀ + (P₀ ^ 2 + P₀ + 3) ^ 2) + P₀ ^ 2 + 4) + 1)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let Rcap := (p + a) ^ a
  let Pcap := p + 2 * Rcap + 6
  have hRcap : 0 ≤ Rcap := by dsimp [Rcap]; positivity
  have hPcap : 0 ≤ Pcap := by dsimp [Pcap]; positivity
  have htotal : Rcap + productNiltestBudget Pcap + 1 ≤ (p + C) ^ C := by
    simpa [X, R₀, P₀, Rcap, Pcap, productNiltestBudget, productObservableLipBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hprod0 : 0 ≤ productNiltestBudget Pcap :=
    (sq_nonneg (Pcap + 2)).trans (productNiltestBudget_geometry hPcap)
  have hRC : Rcap ≤ (p + C) ^ C := by linarith
  have hPC : productNiltestBudget Pcap ≤ (p + C) ^ C := by linarith
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr hRC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q', hsub, hH',
    hshort', hdense, hAq', hq'Z, R', D', hlocal, hbound, hchart, hpair, hlower⟩ := hdata
  obtain ⟨hBound, hFirst, J, hJH, hJ, hJcard, hproduct⟩ :=
    hlocal.product D E T hpA hT V (fun h => ξ * v h)
      (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs
  refine ⟨J, hJH.trans hsub, hJ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hchart.trans hRC))) (Nat.cast_nonneg N)).trans hJcard
  · apply hproduct.mono (hbound.trans hRC)
    · apply le_trans (productNiltestBudget_mono (by positivity) _) hPC
      change _ ≤ p + 2 * Rcap + 6
      change _ ≤ Rcap at hlower hbound
      linarith
    · apply le_trans (productNiltestBudget_mono (by positivity) _) hPC
      change _ ≤ p + 2 * Rcap + 6
      change _ ≤ Rcap at hbound
      linarith

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_orbit_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_F : NativeMixedPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hdimt : ((n + 2 : ℕ) : ℝ) ≤ t := by dsimp [t]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b := by
    exact productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.mixedPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.mixedPairPolynomial) t := by
    have h := F.factorization
    rw [V.mixedPairNiltest_symbol] at h
    have H := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.mixedPairModels).filtration F.basis F.weight F.adapted h hrt
      (fun _ => by exact_mod_cast NeZero.pos N)
    dsimp only [D]
    exact H
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.mixedPairNiltest_complexity.1.mono D htest) (by simpa only [Fintype.card_fin] using hdimt)
    (fun a b => (F.height a b).trans hrt) V.mixedPairPolynomial
    (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
    (fun _ => (Real.exp_le_exp.mpr hcost).trans hN) hfactor
  exact ⟨R.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_outer_control (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1) (n + 2)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.mixedPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
      (fun k => (V.mixedPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixed_pair_top_agreement (x : ℝ ⊗[ℚ] V.MixedPairAlgebra)
    (hx : x ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.mixedPairFrequency_real] at h
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedPairComparison_component_cost : p + 4 ≤ mixedPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hr : 0 ≤ raisedNiltestBudget (p + q) :=
    (add_nonneg hp hq).trans (le_raisedNiltestBudget _)
  unfold mixedPairBudget
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {n : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankIteration
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}

noncomputable def absorbRankZero (W : NativeCorrelationStructure (s + 1) 0 N p f) (hp : 0 ≤ p) :
    NativeMixedCorrelation (s + 1) N (productNiltestBudget (p + 4)) f := by
  have hq : 0 ≤ p + 4 := by linarith
  have hpq : p ≤ productNiltestBudget (p + 4) :=
    (show p ≤ p + 4 by linarith).trans (le_productNiltestBudget hq)
  refine {
    shifts := W.shifts
    nonempty := W.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans W.density
    mixed := W.mixed.mono hpq
    correlation := ?_
  }
  intro h hh
  have hin : Nonempty (NativeVectorCorrelation s N p
      (fun ij : Fin W.mixed.outputDim × Fin W.family.outputDim => fun x =>
        nativeMixedResidual f W.mixed h ij.1 x *
          star ((W.family.lowerComponent ij.2 h).evalCyclic N (fun _ => x)))) := by
    have hc := W.correlation h hh
    change Nonempty (NativeVectorCorrelation s N p
      (fun (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) x =>
        multiplicativeDerivative f h x * star (W.mixed.evalCyclic N ij.1 (correlationInput h x)) *
          star (W.family.evalCyclic N ij.2 h x))) at hc
    simpa only [nativeMixedResidual, NativeDegreeRankFamily.lowerComponent_evalCyclic] using hc
  obtain ⟨V⟩ := hin
  exact NativeVectorCorrelation.exists_absorb
    (W.family.model.dropTop W.family.rankZero_top_eq_bot)
    (fun j => W.family.lowerComponent j h) (nativeMixedResidual f W.mixed h)
    (by linarith : 2 ≤ p + 4) (fun j => W.family.lowerComponent_complexity hp j h)
    (V.mono (by linarith))

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

theorem exists_native_rank_descent (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (_W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hproduct⟩ := exists_native_product_correlation s hs
  obtain ⟨b, _, hvertical⟩ := exists_native_product_verticalization s
  let X : Polynomial ℕ := Polynomial.X
  let R : Polynomial ℕ := X + (X + Polynomial.C a) ^ a + 2
  let Q : Polynomial ℕ := (R + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + Q)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let p₀ := (p + a) ^ a
  let p₁ := p + p₀ + 2
  let p₂ := (p₁ + b) ^ b
  have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
  have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
  have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
  have htotal : p₁ + p₂ ≤ (p + C) ^ C := by
    simpa [X, R, Q, p₀, p₁, p₂, Polynomial.eval₂_pow] using hbudget p hp
  have hpp₁ : p ≤ p₁ := by dsimp [p₁]; linarith
  have hp₀p₁ : p₀ ≤ p₁ := by dsimp [p₁]; linarith
  have hp₀C : p₀ ≤ (p + C) ^ C := by linarith
  have hp₂C : p₂ ≤ (p + C) ^ C := by linarith
  obtain ⟨J, _, hJ, hdense, hcorr⟩ :=
    hproduct W hf ((Real.exp_le_exp.mpr hp₀C).trans hN)
  have hdense' : Real.exp (-p₁) * N ≤ (J.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hp₀p₁))
      (Nat.cast_nonneg _)).trans hdense
  have hdim : (W.mixed.outputDim : ℝ) ≤ Real.exp p₁ :=
    W.mixed.output_bound.trans (Real.exp_le_exp.mpr hpp₁)
  have hI : (Fintype.card (Fin W.family.outputDim) : ℝ) ≤ Real.exp p₁ := by
    simpa only [Fintype.card_fin] using W.family.output_bound.trans (Real.exp_le_exp.mpr hpp₁)
  obtain ⟨V⟩ := hvertical J W.mixed.outputDim hp₁ hf hJ hdense' hdim hI
    (hcorr.mono hp₀p₁ hp₀p₁ hp₀p₁)
  exact ⟨V.mono hp₂C⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_native_rank_zero_reduction (s : ℕ) (hs : 2 ≤ s) (r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (_W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCorrelationStructure s 0 N ((p + C) ^ C) f) := by
  induction r with
  | zero =>
      refine ⟨2, le_rfl, ?_⟩
      intro N _ p f W _ _
      have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
      exact ⟨W.mono (by norm_num; nlinarith [sq_nonneg p])⟩
  | succ r ih =>
      obtain ⟨a, _, hstep⟩ := exists_native_rank_descent s hs
      obtain ⟨b, _, hiterate⟩ := ih
      let X : Polynomial ℕ := Polynomial.X
      let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        (Q + (Q + Polynomial.C b) ^ b)
      refine ⟨C, hC, ?_⟩
      intro N _ p f W hf hN
      have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
      let q := (p + a) ^ a
      let q₂ := (q + b) ^ b
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
      have htotal : q + q₂ ≤ (p + C) ^ C := by
        simpa [X, Q, q, q₂, Polynomial.eval₂_pow] using hbudget p hp
      have hqC : q ≤ (p + C) ^ C := by linarith
      have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
      obtain ⟨W₁⟩ := hstep W hf ((Real.exp_le_exp.mpr hqC).trans hN)
      obtain ⟨W₀⟩ := hiterate W₁ hf ((Real.exp_le_exp.mpr hq₂C).trans hN)
      exact ⟨W₀.mono hq₂C⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedInverseIntervals
namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def toCorrelationStructure (hcor : p + 1 ≤ q) (hq : 2 ≤ q) :
    NativeCorrelationStructure s r N q f := by
  have hpq : p ≤ q := by linarith
  have hq0 : 0 ≤ q := by linarith
  refine {
    shifts := B.shifts
    nonempty := B.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    mixed := NativeMultidegreeNilcharacter.constOne (mixedCorrelationDegree s) hq0
    family := W.toFamily hpq
    correlation := ?_
  }
  intro h hh
  apply NativeVectorCorrelation.exists_of_mean (s - 1) N _ hq
  refine ⟨((0 : Fin 1), (0 : Fin (W.unit.tailDim + 1))), ?_⟩
  have hc := (Real.exp_le_exp.mpr (neg_le_neg hcor)).trans (W.toFamily_correlation hpq h hh)
  simpa only [nativeCorrelationResidual, NativeMultidegreeNilcharacter.constOne_evalCyclic,
    star_one, mul_one] using hc

end Erdos3.NativeDegreeRankDerivativeData

end

section

namespace Erdos3

theorem exists_initial_native_correlation_structure {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeCorrelationStructure s s N ((p + D) ^ D) f) := by
  obtain ⟨a, _, hmodels⟩ := exists_degree_rank_native_inverse_models hI
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C 2)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : (p + a) ^ a + 2 ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hqD : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  obtain ⟨B, ⟨W⟩⟩ := hmodels hp f hf hG
  exact ⟨(W.mono le_rfl hqD).toCorrelationStructure (by linarith) (by linarith)⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_inverse_intervals {s A : ℕ} (hs : 2 ≤ s)
    (hI : CyclicNativeInverse s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ W : NativeCorrelationStructure s 0 N q f,
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ B : NativeRetainedMultilinearIntervalFamily W r,
      ∃ M : NativeMixedCorrelation s N ((p + C) ^ C) f,
        M.shifts = W.shifts ∧ M.mixed.dim = W.mixed.dim ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) M.mixed.eval
          (fun k x => B.mixed.eval k (fun j => x j.1)) := by
  cases s with
  | zero => omega
  | succ s =>
    obtain ⟨a, _, hinitial⟩ := exists_initial_native_correlation_structure hI
    obtain ⟨b, _, hzero⟩ := exists_native_rank_zero_reduction (s + 1) hs (s + 1)
    obtain ⟨c, _, hfamily⟩ := exists_native_retained_multilinear_interval_family (s + 1)
    let X : Polynomial ℕ := Polynomial.X
    let P := (X + Polynomial.C a) ^ a
    let Q := (P + Polynomial.C b) ^ b
    let R := (Q + Polynomial.C c) ^ c
    let T := Q + 4
    let U := (T + 2) ^ 2 + T + (T + (T ^ 2 + T + 3) ^ 2) + T ^ 2 + 4
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R + U)
    refine ⟨C, hC, ?_⟩
    intro N _ p hp hN f hf hG
    let p₀ := (p + a) ^ a
    let q := (p₀ + b) ^ b
    let r := (q + c) ^ c
    have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hu : 0 ≤ productNiltestBudget (q + 4) := by
      unfold productNiltestBudget productObservableLipBudget
      positivity
    have hsum : p₀ + q + r + productNiltestBudget (q + 4) ≤ (p + C) ^ C := by
      simpa [X, P, Q, R, T, U, p₀, q, r, productNiltestBudget,
        productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp
    have hqC : q ≤ (p + C) ^ C := by linarith
    have hrC : r ≤ (p + C) ^ C := by linarith
    have huC : productNiltestBudget (q + 4) ≤ (p + C) ^ C := by linarith
    obtain ⟨W₁⟩ := hinitial hp f hf hG
    obtain ⟨W⟩ := hzero W₁ hf ((Real.exp_le_exp.mpr hqC).trans hN)
    obtain ⟨B⟩ := hfamily W hf
    let M := (W.absorbRankZero hq).mono huC
    exact ⟨q, hq, hqC, W, r, hr, hrC, B, M, rfl, rfl, B.equivalence.mono hrC⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_unit_row_model_with_differences (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ (f : ZMod N → ℂ) (R : (Unit → ℤ) → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p R) →
      Real.exp (-p) ≤ ‖𝔼 n : ZMod N, f n * star (R (fun _ => (n.val : ℤ)))‖ →
      ∃ g : (Unit → ℤ) → ℂ,
        (∀ x, ‖g x‖ ≤ 1) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) g) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n : ZMod N, f n * star (g (fun _ => (n.val : ℤ)))‖ ∧
        ∀ {e : ℝ}, 0 ≤ e → Real.exp (e + 16) ≤ (N : ℝ) →
          ∀ k : ZMod N, ∃ K : (Unit → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
            (𝔼 n : ZMod N,
              ‖g (fun _ => (n.val : ℤ)) * star (g (fun _ => ((n + k).val : ℤ))) -
                K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hunit⟩ := RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hdifference⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_univariate_cyclic_difference_models s hs
  let X : Polynomial ℕ := Polynomial.X
  let U := (2 * X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + 4 + (U + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f R hf hR hcorr
  let sample (_ : Unit) (n : ZMod N) : Unit → ℤ := fun _ => (n.val : ℤ)
  have hc : Real.exp (-p) ≤ 𝔼 _h : Unit, ‖𝔼 n : ZMod N, f n * star (R (sample () n))‖ := by
    simpa only [Fintype.expect_const] using hcorr
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion (Classical.choice hR) hp hc
  have hpp : p + p = 2 * p := by ring
  rw [hpp] at P
  obtain ⟨n, hn, hncard, V, hD, hV⟩ := hunit P.model P.test
    (by positivity : 0 ≤ 2 * p) P.complexity sample (fun _ n => f n) (fun _ n => hf n) P.correlation
  let u := (2 * p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 4 + (u + p + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u + 4 ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have huC' : u ≤ (p + C) ^ C := by linarith
  let g : (Unit → ℤ) → ℂ := (V.test P.test.orbit 0).eval
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hncard
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (V.test P.test.orbit 0).norm_eval_le x
  · exact ⟨(NativeIntegerExpansion.ofTest (V.test P.test.orbit 0)
      (V.test_complexity P.test.orbit hu hD 0) (fun _ => rfl)).mono huC⟩
  · apply (Real.exp_le_exp.mpr (neg_le_neg huC')).trans
    simpa only [sample, Fintype.expect_const] using hV
  · intro e he hN k
    obtain ⟨K, ⟨E⟩, herr⟩ := hdifference P.model V P.test.orbit hu hD hcard he hN 0 0 k
    have hcost : (u + e + B) ^ B ≤ (p + e + C) ^ C := by
      have hu' : u ≤ (2 * (p + e) + A) ^ A :=
        pow_le_pow_left₀ (by positivity) (by linarith) A
      have hb : (2 * (p + e) + A) ^ A + 4 +
          ((2 * (p + e) + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
        simpa [X, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
      apply le_trans _ ((le_add_of_nonneg_left (by positivity)).trans hb)
      exact pow_le_pow_left₀ (by positivity) (by linarith) B
    exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem dense_set_mean_lower_bound {I : Type*} [Fintype I] [Nonempty I]
    (H : Finset I) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) {α δ : ℝ} (hδ : 0 ≤ δ)
    (hdensity : α * Fintype.card I ≤ (H.card : ℝ))
    (hlarge : ∀ i ∈ H, δ ≤ f i) : α * δ ≤ 𝔼 i, f i := by
  classical
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 i : I, if i ∈ H then δ else 0) =
      (H.card : ℝ) * δ / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  calc
    _ ≤ (H.card : ℝ) * δ / Fintype.card I := by
      apply (le_div_iff₀ hcard).mpr
      nlinarith [mul_le_mul_of_nonneg_right hdensity hδ]
    _ = _ := hindicator.symm
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro i _
      split_ifs with hi
      · exact hlarge i hi
      · exact hf i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unit_row_family_with_differences (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H : Type*} [Fintype H] [Nonempty H] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → ∀ (F : H → ZMod N → ℂ) (R : H → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (R h (fun _ => (n.val : ℤ)))‖) →
      ∃ g : H → (Unit → ℤ) → ℂ,
        (∀ h x, ‖g h x‖ ≤ 1) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) (g h))) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖) ∧
        ∀ {e : ℝ}, 0 ≤ e → Real.exp (e + 16) ≤ (N : ℝ) →
          ∀ (h : H) (k : ZMod N), ∃ K : (Unit → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
            (𝔼 n : ZMod N,
              ‖g h (fun _ => (n.val : ℤ)) * star (g h (fun _ => ((n + k).val : ℤ))) -
                K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hmodel⟩ := exists_unit_row_model_with_differences s hs
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 2
  let U := (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + U + 2)
  refine ⟨C, hC, ?_⟩
  intro H _ _ N _ p hp F R hF hR hE hcorr
  classical
  let t := p + 2
  let a := (t + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum : t + a + 2 ≤ (p + C) ^ C := by
    simpa [X, T, U, t, a, Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have htaC : t + a ≤ (p + C) ^ C := by linarith
  have htwo : 2 ≤ (p + C) ^ C := by linarith
  have hcost (e : ℝ) (he : 0 ≤ e) : (t + e + A) ^ A ≤ (p + e + C) ^ C := by
    have hh : (p + e + 2) + (p + e + 2 + A) ^ A + 2 ≤ (p + e + C) ^ C := by
      simpa [X, T, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
    have heq : t + e + A = p + e + 2 + A := by dsimp [t]; ring
    rw [heq]
    linarith
  have htwo' (e : ℝ) (he : 0 ≤ e) : 2 ≤ (p + e + C) ^ C := by
    have hh : (p + e + 2) + (p + e + 2 + A) ^ A + 2 ≤ (p + e + C) ^ C := by
      simpa [X, T, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
    have hpow : 0 ≤ (p + e + 2 + A) ^ A := by positivity
    linarith
  let c (h : H) := ‖𝔼 n : ZMod N, F h n * star (R h (fun _ => (n.val : ℤ)))‖
  have hcap (h : H) : c h ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set c (Real.exp_nonneg (-p)) hcap hcorr
  have hhalf : Real.exp (-t) ≤ Real.exp (-p) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hgood (h : H) (hh : h ∈ S) :=
    hmodel ht (F h) (R h) (hF h) ⟨(Classical.choice (hE h)).mono hpt⟩
      (hhalf.trans (hlarge h hh))
  let g₀ (h : H) (hh : h ∈ S) := Classical.choose (hgood h hh)
  have hg₀ (h : H) (hh : h ∈ S) := Classical.choose_spec (hgood h hh)
  let g : H → (Unit → ℤ) → ℂ := fun h => if hh : h ∈ S then g₀ h hh else fun _ => 1
  have hg (h : H) (hh : h ∈ S) : g h = g₀ h hh := dif_pos hh
  have hgnot (h : H) (hh : h ∉ S) : g h = fun _ => 1 := dif_neg hh
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro h x
    by_cases hh : h ∈ S
    · rw [hg h hh]
      exact (hg₀ h hh).1 x
    · rw [hgnot h hh]
      simp
  · intro h
    by_cases hh : h ∈ S
    · rw [hg h hh]
      exact ⟨(Classical.choice (hg₀ h hh).2.1).mono haC⟩
    · rw [hgnot h hh]
      exact ⟨NativeIntegerExpansion.constOne _ _ htwo⟩
  · have hmass := dense_set_mean_lower_bound S
      (fun h => ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖)
      (fun _ => norm_nonneg _) (Real.exp_nonneg (-a))
      ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) (by
        intro h hh
        rw [hg h hh]
        exact (hg₀ h hh).2.2.1)
    apply (Real.exp_le_exp.mpr (neg_le_neg htaC)).trans
    have heq : Real.exp (-(t + a)) = Real.exp (-t) * Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq]
  · intro e he hN h k
    by_cases hh : h ∈ S
    · obtain ⟨K, ⟨E⟩, herr⟩ := (hg₀ h hh).2.2.2 he hN k
      refine ⟨K, ⟨E.mono (hcost e he)⟩, ?_⟩
      simpa only [hg h hh] using herr
    · refine ⟨fun _ => 1, ⟨NativeIntegerExpansion.constOne _ _ (htwo' e he)⟩, ?_⟩
      simp only [hgnot h hh, star_one, mul_one, sub_self, norm_zero, Finset.expect_const_zero]
      exact Real.exp_nonneg _

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_residual_row_differences_degree (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 3) d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (F : ZMod N → ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 2) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        (F h n * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
      ∃ J : ZMod N → ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + C) ^ C) (K k))) ∧
        (∀ k h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) (J k h))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
            star (J k h (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model (s + 3)
  obtain ⟨B, _, hrows⟩ := exists_unit_row_family_with_differences (s + 1) (by omega)
  obtain ⟨D₀, _, hcyclic⟩ :=
    UnitVerticalObservable.exists_cyclic_second_difference_models_degree (s + 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let T₀ := X + Q + 4
  let V₀ := (T₀ + Polynomial.C B) ^ B
  let E₁ := 2 * V₀ + 4
  let A₀ := (Q + E₁ + Polynomial.C D₀) ^ D₀
  let E₂ := E₁ + 2 * A₀
  let B₀ := (T₀ + E₂ + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + B₀ + 2 * V₀ + E₂ + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN F R hF hR hRE hcorr
  classical
  let q := (p + A) ^ A
  let t := p + q + 4
  let v := (t + B) ^ B
  let e₁ := 2 * v + 4
  let a := (q + e₁ + D₀) ^ D₀
  let e₂ := e₁ + 2 * a
  let b := (t + e₂ + B) ^ B
  let z := 2 * v + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp [e₂]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hsum : a + b + 2 * v + e₂ + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, T₀, V₀, E₁, A₀, E₂, B₀, q, t, v, e₁, a, e₂, b,
      Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hzC : z ≤ (p + C) ^ C := by dsimp [z]; linarith
  have hN₁ : Real.exp (e₁ + 16) ≤ (N : ℝ) := by
    apply (Real.exp_le_exp.mpr ?_).trans hN
    dsimp [e₂] at hsum
    linarith
  have hN₂ : Real.exp (e₂ + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n => F h n * star (R h (fun _ => (n.val : ℤ)))) (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)) hcorr
  let u (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hu (h n : ZMod N) : ‖u h n‖ ≤ 1 := (V.test T.orbit 0).norm_eval_le _
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hrowcorr : Real.exp (-t) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      (F h n * star (u h n)) * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans
    apply hVcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨G, hG, _, hGcorr, hGdiff⟩ := hrows ht
    (fun h n => F h n * star (u h n)) R (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hu h n)) hR
    (fun h => ⟨(Classical.choice (hRE h)).mono hpt⟩) hrowcorr
  have hbase : Real.exp (-v) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (u h n * G h (fun _ => (n.val : ℤ)))‖) := by
    simpa only [star_mul, mul_comm, mul_left_comm, mul_assoc] using hGcorr
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) a K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e₁) :=
    hcyclic D V T.orbit hq hD hcard he₁ hN₁ 0 0 k
  choose K hK herrK using hmodels
  have hrowmodels (k h : ZMod N) : ∃ J : (Unit → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) b J) ∧
      (𝔼 n : ZMod N,
        ‖G h (fun _ => (n.val : ℤ)) * star (G h (fun _ => ((n + k).val : ℤ))) -
          J (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e₂) :=
    hGdiff he₂ hN₂ h k
  choose J hJ herrJ using hrowmodels
  have hd := mean_row_correlation_sq_le_product_derivatives F u
    (fun h n => G h (fun _ => (n.val : ℤ)))
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)])
    (fun k h n => J k h (fun _ => (n.val : ℤ)))
    (B := Real.exp (2 * a)) (ε := Real.exp (-e₁)) (δ := Real.exp (-e₂))
    hF (fun h n => hG h _) (Real.exp_nonneg _) (by
      intro k h n
      exact (Classical.choice (hK k)).norm_eval_le _) (by
      intro k h
      simpa only [u, multiplicativeDerivative, cyclicSecondDifference] using herrK k h.val) (by
      intro k h
      simpa only [multiplicativeDerivative] using herrJ k h)
  have hlarge : Real.exp (-(2 * v)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
        star (J k h (fun _ => (n.val : ℤ)))‖) +
          (Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂)) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-v)) hbase 2).trans hd
    have hexp : Real.exp (-v) ^ 2 = Real.exp (-(2 * v)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [hexp, star_mul, mul_comm, mul_left_comm, mul_assoc] using hsquare
  have herror : Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂) ≤ Real.exp (-z) := by
    have hmul : Real.exp (2 * a) * Real.exp (-e₂) = Real.exp (-e₁) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [e₂]
      ring
    rw [hmul]
    calc
      _ = 2 * Real.exp (-e₁) := by ring
      _ ≤ Real.exp 2 * Real.exp (-e₁) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e₁, z]; ring
  have htwo : 2 * Real.exp (-z) ≤ Real.exp (-(2 * v)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-z) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [z]; ring
  refine ⟨K, J, fun k => ⟨(Classical.choice (hK k)).mono haC⟩,
    fun k h => ⟨(Classical.choice (hJ k h)).mono hbC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg hzC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


