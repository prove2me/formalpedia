-- Prove2me | Definitions.Def_SourceProof_5e9757a88ef83b24bbaf0d97
-- name    : SourceProof_5e9757a88ef83b24bbaf0d97
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:04:13.761687+00:00
-- url     : https://prove2.me/theorems/cc2f9300-34f5-42b5-93ef-fa04662239e9
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.integral_charlierPoly_mul
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Charlier_F001
import Definitions.Def_SourceProof_6e9f626cac2025a847c81060

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Charlier polynomials and their Poisson orthogonality

The Charlier polynomials with parameter `lam` are given by the recursion
`C_(s+1)(x) = x C_s(x - 1) - lam C_s(x)` from `C_0 = 1`, the backward-difference analogue of the
Hermite recursion `H_(n+1) = (x - v d/dx) H_n`; their exponential generating function is
`e^(-lam t) (1 + t) ^ x`. The forward difference plays the role the derivative plays there,
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`, and the degree-two member is
`C_2(x; lam) = (x - lam) ^ 2 - x`. The parameter is the mean of the Poisson law that makes the
family orthogonal: under the Poisson law of mean `r` the family with parameter `r` satisfies
`E[C_s C_t] = δ_(s t) s! r ^ s`.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_succ` — the recursion at the level of values.
* `LevyStochCalc.Probability.charlierScaled_two` — `C_2(x; lam) = (x - lam) ^ 2 - x`.
* `LevyStochCalc.Probability.charlierScaled_forward_diff` —
  `C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`.
* `LevyStochCalc.Probability.integral_charlierPoly_mul` — `E[C_s C_t] = δ_(s t) s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_sq` — `E[C_s ^ 2] = s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_eq_zero` — `E[C_s] = 0` for `s ≠ 0`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat


theorem _root_.Prove2MeSourceProof.h_5e9757a88ef83b24bbaf0d97 (r : ℝ≥0) (s t : ℕ) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) * (charlierPoly (r : ℝ) t).eval (n : ℝ)
        ∂poissonMeasure r
      = if s = t then (s.factorial : ℝ) * (r : ℝ) ^ s else 0 := by
  induction s generalizing t with
  | zero =>
    simp only [charlierPoly_zero, eval_one, one_mul, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one]
    induction t with
    | zero => simp
    | succ t _ =>
      have h := LevyStochCalc.Probability.integral_charlier_step r (LevyStochCalc.Probability.charlierPoly (r : ℝ) t) 1
      simp only [eval_one, mul_one, sub_self, mul_zero, integral_zero, mul_zero] at h
      simp only [charlierPoly_succ, eval_sub, eval_mul, eval_X, eval_C, eval_comp]
      simpa using h
  | succ s ih =>
    have hstep := LevyStochCalc.Probability.integral_charlier_step r (LevyStochCalc.Probability.charlierPoly (r : ℝ) s) (LevyStochCalc.Probability.charlierPoly (r : ℝ) t)
    simp only [charlierPoly_succ, eval_sub, eval_mul, eval_X, eval_C, eval_comp]
    rw [hstep]
    cases t with
    | zero => simp
    | succ u =>
      have hfd : ∀ n : ℕ, (LevyStochCalc.Probability.charlierPoly (r : ℝ) (u + 1)).eval ((n : ℝ) + 1)
          - (LevyStochCalc.Probability.charlierPoly (r : ℝ) (u + 1)).eval (n : ℝ)
          = ((u : ℝ) + 1) * (LevyStochCalc.Probability.charlierPoly (r : ℝ) u).eval (n : ℝ) := by
        intro n
        simpa [charlierScaled] using _root_.Prove2MeSourceProof.h_6e9f626cac2025a847c81060 u (r : ℝ) (n : ℝ)
      simp_rw [hfd]
      have e : ∀ n : ℕ, (LevyStochCalc.Probability.charlierPoly (r : ℝ) s).eval (n : ℝ)
          * (((u : ℝ) + 1) * (LevyStochCalc.Probability.charlierPoly (r : ℝ) u).eval (n : ℝ))
          = ((u : ℝ) + 1) * ((LevyStochCalc.Probability.charlierPoly (r : ℝ) s).eval (n : ℝ)
            * (LevyStochCalc.Probability.charlierPoly (r : ℝ) u).eval (n : ℝ)) := by
        intro n; ring
      simp_rw [e]
      rw [integral_const_mul, ih u]
      by_cases hsu : s = u
      · subst hsu
        rw [if_pos rfl, if_pos rfl]
        simp only [Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hsu, if_neg (by omega)]
        ring
end LevyStochCalc.Probability


