-- Prove2me | Definitions.Def_LevyStochCalc_Probability_EmpiricalMean_F000
-- name    : LevyStochCalc_Probability_EmpiricalMean_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:01:57.799187+00:00
-- url     : https://prove2.me/theorems/8652a4a5-2a3c-4725-be96-4f636ce330ca
-- title:
--   Source declarations: LevyStochCalc.Probability.EmpiricalMean
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.EmpiricalMean. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Moments.Variance

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Variance and concentration of an empirical mean

For `N` pairwise independent square-integrable real random variables whose variances are at most
`B`, the empirical mean `(1/N) ∑ Xᵢ` has variance at most `B / N`, and Chebyshev's inequality turns
this into the deviation bound `μ {c ≤ |X̄ - 𝔼 X̄|} ≤ B / (N c²)`.

## Main statements

* `LevyStochCalc.Probability.variance_empiricalMean_le` — `Var((1/N) ∑ Xᵢ) ≤ B / N`.
* `LevyStochCalc.Probability.empiricalMean_concentration` — the Chebyshev tail
  `μ {c ≤ |X̄ - 𝔼 X̄|} ≤ B / (N c²)`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The empirical mean `(1/N) ∑ Xᵢ` of `N` pairwise independent square-integrable real random
variables, each of variance at most `B`, has variance at most `B / N`. -/
theorem variance_empiricalMean_le {N : ℕ} (X : Fin N → Ω → ℝ) (B : ℝ)
    (hmem : ∀ i, MemLp (X i) 2 μ)
    (hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin N))) (fun i j => IndepFun (X i) (X j) μ))
    (hvar : ∀ i, variance (X i) μ ≤ B) :
    variance ((N : ℝ)⁻¹ • (∑ i, X i)) μ ≤ B / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [variance_smul, IndepFun.variance_sum (fun i _ => hmem i) hindep]
  have hsum : ∑ i, variance (X i) μ ≤ (N : ℝ) * B := by
    calc ∑ i, variance (X i) μ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => hvar i)
      _ = (N : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ((N : ℝ)⁻¹) ^ 2 * ∑ i, variance (X i) μ
      ≤ ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B / N := by field_simp
/-- Chebyshev's inequality for the empirical mean: for `N` pairwise independent square-integrable
real random variables, each of variance at most `B`, and `c > 0`, the empirical mean
`X̄ = (1/N) ∑ Xᵢ` satisfies `μ {c ≤ |X̄ - 𝔼 X̄|} ≤ B / (N c²)`. -/
theorem empiricalMean_concentration [IsProbabilityMeasure μ] {N : ℕ}
    (X : Fin N → Ω → ℝ) (B c : ℝ) (hc : 0 < c)
    (hmem : ∀ i, MemLp (X i) 2 μ)
    (hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin N))) (fun i j => IndepFun (X i) (X j) μ))
    (hvar : ∀ i, variance (X i) μ ≤ B) :
    μ {ω | c ≤ |((N : ℝ)⁻¹ • (∑ i, X i)) ω - μ[(N : ℝ)⁻¹ • (∑ i, X i)]|}
      ≤ ENNReal.ofReal (B / (N * c ^ 2)) := by
  have hmemMean : MemLp ((N : ℝ)⁻¹ • (∑ i, X i)) 2 μ :=
    (memLp_finsetSum' _ (fun i _ => hmem i)).const_smul _
  refine le_trans (meas_ge_le_variance_div_sq hmemMean hc) ?_
  apply ENNReal.ofReal_le_ofReal
  have hvb := variance_empiricalMean_le X B hmem hindep hvar
  calc variance ((N : ℝ)⁻¹ • (∑ i, X i)) μ / c ^ 2
      ≤ (B / N) / c ^ 2 := div_le_div_of_nonneg_right hvb (sq_nonneg c)
    _ = B / (N * c ^ 2) := by rw [div_div]
end LevyStochCalc.Probability


