-- Prove2me | Definitions.Def_SourceProof_431e64ab8e52f44314251e91
-- name    : SourceProof_431e64ab8e52f44314251e91
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:49:06.904188+00:00
-- url     : https://prove2.me/theorems/5a7f5641-0425-4134-9fa1-a6515dd55002
-- title:
--   LevyStochCalc source module: SourceProof_431e64ab8e52f44314251e91
-- statement:
--   The original source theorem `LevyStochCalc.Probability.integral_hermitePoly_mul` comes from the `LevyStochCalc.Probability.Hermite` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Hermite polynomials of variance `v` and their Gaussian orthogonality

The probabilists' Hermite polynomials of variance `v` are given by the Appell recursion
`H_(n+1) = (x - v d/dx) H_n`, which makes the derivative `H_(n+1)' = (n+1) H_n` and the three-term
recursion `H_(n+2) = x H_(n+1) - (n+1) v H_n` immediate. For `v > 0` they rescale Mathlib's
family `Polynomial.hermite` by `H_n(x; v) = √v ^ n * He_n(x / √v)`, and `H_2(x; v) = x ^ 2 - v`.
Under the law `gaussianReal 0 v` they are orthogonal, with `E[H_n H_m] = δ_(n m) n! v ^ n`.

The opening section adds the derivative and the three-term recursion of Mathlib's
`Polynomial.hermite`, both of which belong with `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`.

## Main statements

* `Polynomial.derivative_hermite` — `He_(n+1)' = (n+1) He_n`.
* `Polynomial.hermite_succ_succ` — `He_(n+2) = X He_(n+1) - (n+1) He_n`.
* `LevyStochCalc.Probability.derivative_hermitePoly` — `H_(n+1)' = (n+1) H_n`.
* `LevyStochCalc.Probability.hermitePoly_succ_succ` — `H_(n+2) = X H_(n+1) - (n+1) v H_n`.
* `LevyStochCalc.Probability.hermiteScaled_two` — `H_2(x; v) = x ^ 2 - v`.
* `LevyStochCalc.Probability.hermiteScaled_eq` — `H_n(x; v) = √v ^ n * He_n(x / √v)` for `v > 0`.
* `LevyStochCalc.Probability.integral_hermitePoly_mul` — `E[H_n H_m] = δ_(n m) n! v ^ n`.
-/

namespace Polynomial

end Polynomial

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal


theorem _root_.Prove2MeSourceProof.h_431e64ab8e52f44314251e91 (v : ℝ≥0) (n m : ℕ) :
    ∫ x, (hermitePoly (v : ℝ) n).eval x * (hermitePoly (v : ℝ) m).eval x ∂gaussianReal 0 v
      = if n = m then (n.factorial : ℝ) * (v : ℝ) ^ n else 0 := by
  induction n generalizing m with
  | zero =>
    simp only [hermitePoly_zero, eval_one, one_mul, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one]
    induction m with
    | zero => simp
    | succ m _ =>
      have h := LevyStochCalc.Probability.integral_hermite_step v (LevyStochCalc.Probability.hermitePoly (v : ℝ) m) 1
      simp only [derivative_one, eval_zero, mul_zero, integral_zero, mul_zero, eval_one,
        mul_one] at h
      rw [LevyStochCalc.Probability.hermitePoly_succ]
      simp only [eval_sub, eval_mul, eval_X, eval_C]
      rw [h]
      simp
  | succ n ih =>
    rw [LevyStochCalc.Probability.hermitePoly_succ]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    rw [LevyStochCalc.Probability.integral_hermite_step v (LevyStochCalc.Probability.hermitePoly (v : ℝ) n) (LevyStochCalc.Probability.hermitePoly (v : ℝ) m)]
    cases m with
    | zero => simp
    | succ k =>
      rw [LevyStochCalc.Probability.derivative_hermitePoly]
      simp only [eval_mul, eval_C]
      rw [show (fun x : ℝ => (LevyStochCalc.Probability.hermitePoly (v : ℝ) n).eval x * (((k : ℝ) + 1) *
          (LevyStochCalc.Probability.hermitePoly (v : ℝ) k).eval x)) = fun x : ℝ => ((k : ℝ) + 1) *
          ((LevyStochCalc.Probability.hermitePoly (v : ℝ) n).eval x * (LevyStochCalc.Probability.hermitePoly (v : ℝ) k).eval x) from by
        funext x; ring]
      rw [integral_const_mul, ih k]
      by_cases hnk : n = k
      · subst hnk
        simp only [Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hnk, if_neg (by omega)]
        ring
end LevyStochCalc.Probability


