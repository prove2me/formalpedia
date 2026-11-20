-- Prove2me | Definitions.Def_SourceProof_b6e0ed871fbe873258573769
-- name    : SourceProof_b6e0ed871fbe873258573769
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:28:49.225992+00:00
-- url     : https://prove2.me/theorems/8228e844-b584-4409-b14e-f444f871571e
-- title:
--   LevyStochCalc source module: SourceProof_b6e0ed871fbe873258573769
-- statement:
--   The original source theorem `LevyStochCalc.Probability.integral_mul_eval_gaussianReal` comes from the `LevyStochCalc.Probability.GaussianMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_GaussianMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a centred real Gaussian and Gaussian integration by parts

For the law `gaussianReal 0 v` on `ℝ` the even moments are `E[X^(2n)] = v^n (2n-1)!!`, the odd
moments vanish, and the two are tied together by the recursion `E[X^(k+2)] = (k+1) v E[X^k]`.
Every polynomial function is integrable for this law, and the Stein identity
`E[X p(X)] = v E[p'(X)]` holds for every real polynomial `p`.

## Main statements

* `LevyStochCalc.Probability.integral_pow_even_gaussianReal` — `E[X^(2n)] = v^n (2n-1)!!`.
* `LevyStochCalc.Probability.integral_pow_odd_gaussianReal` — `E[X^(2n+1)] = 0`.
* `LevyStochCalc.Probability.integral_pow_add_two_gaussianReal` — `E[X^(k+2)] = (k+1) v E[X^k]`.
* `LevyStochCalc.Probability.integrable_eval_gaussianReal` — `p(X)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_gaussianReal` — `E[X p(X)] = v E[p'(X)]`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

variable (v : ℝ≥0)


theorem _root_.Prove2MeSourceProof.h_b6e0ed871fbe873258573769 (p : ℝ[X]) :
    ∫ x, x * p.eval x ∂gaussianReal 0 v
      = (v : ℝ) * ∫ x, (derivative p).eval x ∂gaussianReal 0 v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h1 : Integrable (fun x : ℝ => x * p.eval x) (gaussianReal 0 v) := by
      have h := LevyStochCalc.Probability.integrable_eval_gaussianReal v (X * p)
      simpa only [eval_mul, eval_X] using h
    have h2 : Integrable (fun x : ℝ => x * q.eval x) (gaussianReal 0 v) := by
      have h := LevyStochCalc.Probability.integrable_eval_gaussianReal v (X * q)
      simpa only [eval_mul, eval_X] using h
    have h3 : Integrable (fun x : ℝ => (derivative p).eval x) (gaussianReal 0 v) :=
      LevyStochCalc.Probability.integrable_eval_gaussianReal v _
    have h4 : Integrable (fun x : ℝ => (derivative q).eval x) (gaussianReal 0 v) :=
      LevyStochCalc.Probability.integrable_eval_gaussianReal v _
    simp only [eval_add, derivative_add, mul_add]
    rw [integral_add h1 h2, integral_add h3 h4, hp, hq]
    ring
  | monomial n a =>
    rcases n with _ | k
    · simp only [monomial_zero_left, eval_C, derivative_C, eval_zero, integral_zero, mul_zero]
      simp_rw [mul_comm _ a]
      rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
    · have hev : ∀ x : ℝ, x * (monomial (k + 1) a).eval x = a * x ^ (k + 2) := by
        intro x; rw [eval_monomial]; ring
      have hdv : derivative (monomial (k + 1) a) = monomial k (((k : ℝ) + 1) * a) := by
        rw [derivative_monomial]
        congr 1
        push_cast
        ring
      simp_rw [hev, hdv, eval_monomial]
      rw [integral_const_mul, integral_const_mul, LevyStochCalc.Probability.integral_pow_add_two_gaussianReal]
      ring
end LevyStochCalc.Probability


