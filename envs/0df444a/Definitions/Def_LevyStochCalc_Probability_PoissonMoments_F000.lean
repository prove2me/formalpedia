-- Prove2me | Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F000
-- name    : LevyStochCalc_Probability_PoissonMoments_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:06:53.739193+00:00
-- url     : https://prove2.me/theorems/ee321d23-a0f3-4d52-898f-dce8acf24492
-- title:
--   Source declarations: LevyStochCalc.Probability.PoissonMoments
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.PoissonMoments. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Poisson law and Poisson integration by parts

The law `poissonMeasure r` on `ℕ` gives the atom `n` the mass `exp (-r) * r ^ n / n !`, so it is
the Poisson law of mean `r`. Every polynomial function is integrable for it, and the Stein
identity `E[N p(N)] = r E[p(N + 1)]` holds for every real polynomial `p`, with the forward shift
in place of the derivative of the Gaussian identity. Mean and variance are both `r`, the
factorial moments are `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`, the third central moment is `r` and
the fourth central moment is `3 r ^ 2 + r`. The identity has moments of every finite order.

## Main statements

* `LevyStochCalc.Probability.integrable_eval_poissonMeasure` — `p(N)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_poissonMeasure` — `E[N p(N)] = r E[p(N + 1)]`.
* `LevyStochCalc.Probability.integral_id_poissonMeasure` — `E[N] = r`.
* `LevyStochCalc.Probability.integral_id_sq_poissonMeasure` — `E[N ^ 2] = r ^ 2 + r`.
* `LevyStochCalc.Probability.integral_sub_sq_poissonMeasure` — `E[(N - r) ^ 2] = r`.
* `LevyStochCalc.Probability.integral_descPochhammer_eval_poissonMeasure` — the factorial
  moments `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`.
* `LevyStochCalc.Probability.integral_sub_pow_three_poissonMeasure` — `E[(N - r) ^ 3] = r`.
* `LevyStochCalc.Probability.integral_sub_pow_four_poissonMeasure` —
  `E[(N - r) ^ 4] = 3 r ^ 2 + r`.
* `LevyStochCalc.Probability.memLp_natCast_poissonMeasure` — `N ∈ Lᵖ` for every finite `p`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

/-- Every power is integrable for a Poisson law. -/
theorem integrable_pow_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    Integrable (fun n : ℕ => (n : ℝ) ^ k) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hbd : ∀ n : ℕ, Real.exp (-r) * (r : ℝ) ^ n / n ! * ‖(n : ℝ) ^ k‖
      ≤ Real.exp (-r) * (k ! : ℝ) * (((r : ℝ) * Real.exp 1) ^ n / n !) := by
    intro n
    have h1 : (n : ℝ) ^ k / k ! ≤ Real.exp n :=
      Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) k
    have hk : (0 : ℝ) < k ! := by positivity
    have h2 : (n : ℝ) ^ k ≤ (k ! : ℝ) * Real.exp n := by
      rw [div_le_iff₀ hk] at h1; linarith [h1]
    have h3 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hnorm : ‖(n : ℝ) ^ k‖ = (n : ℝ) ^ k := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hfac : (0 : ℝ) < n ! := by positivity
    rw [hnorm]
    rw [h3] at h2
    have hrn : (0 : ℝ) ≤ Real.exp (-r) * (r : ℝ) ^ n / n ! := by positivity
    have key : Real.exp (-r) * (r : ℝ) ^ n / n ! * (n : ℝ) ^ k
        ≤ Real.exp (-r) * (r : ℝ) ^ n / n ! * ((k ! : ℝ) * Real.exp 1 ^ n) :=
      mul_le_mul_of_nonneg_left h2 hrn
    refine key.trans_eq ?_
    field_simp
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) hbd ?_
  exact ((Real.summable_pow_div_factorial ((r : ℝ) * Real.exp 1)).mul_left _)
/-- The identity is integrable for a Poisson law. -/
theorem integrable_id_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  simpa using integrable_pow_poissonMeasure r 1
/-- Every polynomial function is integrable for a Poisson law. -/
theorem integrable_eval_poissonMeasure (r : ℝ≥0) (p : ℝ[X]) :
    Integrable (fun n : ℕ => p.eval (n : ℝ)) (poissonMeasure r) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.add hq
  | monomial n a =>
    simpa [eval_monomial] using (integrable_pow_poissonMeasure r n).const_mul a
/-- Every polynomial function of the forward shift is integrable for a Poisson law. -/
theorem integrable_eval_add_one_poissonMeasure (r : ℝ≥0) (p : ℝ[X]) :
    Integrable (fun n : ℕ => p.eval ((n : ℝ) + 1)) (poissonMeasure r) := by
  have h := integrable_eval_poissonMeasure r (p.comp (X + C 1))
  simpa [eval_comp] using h
end LevyStochCalc.Probability


