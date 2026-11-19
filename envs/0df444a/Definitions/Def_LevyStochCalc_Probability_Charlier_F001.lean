-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Charlier_F001
-- name    : LevyStochCalc_Probability_Charlier_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:40:50.03619+00:00
-- url     : https://prove2.me/theorems/9a4f32f3-5fd8-4a8a-b529-09f394a0de86
-- title:
--   Source declarations: LevyStochCalc.Probability.Charlier
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.Charlier. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F001
import Mathlib.Topology.Algebra.Polynomial

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

/-- One step of the Charlier recursion under the Poisson law of mean `r`: the recursion term
`n p(n - 1) - r p(n)` of the first factor becomes `r` times the forward difference of the second
factor. -/
theorem integral_charlier_step (r : ℝ≥0) (p q : ℝ[X]) :
    ∫ n : ℕ, ((n : ℝ) * p.eval ((n : ℝ) - 1) - (r : ℝ) * p.eval (n : ℝ)) * q.eval (n : ℝ)
        ∂poissonMeasure r
      = (r : ℝ) * ∫ n : ℕ, p.eval (n : ℝ) * (q.eval ((n : ℝ) + 1) - q.eval (n : ℝ))
        ∂poissonMeasure r := by
  have hA : Integrable (fun n : ℕ => (n : ℝ) * (p.comp (X - C 1) * q).eval (n : ℝ))
      (poissonMeasure r) := by
    have h := integrable_eval_poissonMeasure r (X * (p.comp (X - C 1) * q))
    simpa only [eval_mul, eval_X] using h
  have hB : Integrable (fun n : ℕ => (r : ℝ) * (p * q).eval (n : ℝ)) (poissonMeasure r) :=
    (integrable_eval_poissonMeasure r (p * q)).const_mul _
  have hC : Integrable (fun n : ℕ => p.eval (n : ℝ) * q.eval ((n : ℝ) + 1))
      (poissonMeasure r) := by
    have h := integrable_eval_poissonMeasure r (p * q.comp (X + C 1))
    simpa only [eval_mul, eval_comp, eval_add, eval_X, eval_C] using h
  have hD : Integrable (fun n : ℕ => p.eval (n : ℝ) * q.eval (n : ℝ)) (poissonMeasure r) := by
    have h := integrable_eval_poissonMeasure r (p * q)
    simpa only [eval_mul] using h
  have e : ∀ n : ℕ, ((n : ℝ) * p.eval ((n : ℝ) - 1) - (r : ℝ) * p.eval (n : ℝ)) * q.eval (n : ℝ)
      = (n : ℝ) * (p.comp (X - C 1) * q).eval (n : ℝ) - (r : ℝ) * (p * q).eval (n : ℝ) := by
    intro n; simp only [eval_mul, eval_comp, eval_sub, eval_X, eval_C]; ring
  simp_rw [e]
  rw [integral_sub hA hB, _root_.Prove2MeSourceProof.h_2ee02b5cd77c741d226b69cf r (p.comp (X - C 1) * q),
    integral_const_mul]
  have e2 : ∀ n : ℕ, (p.comp (X - C 1) * q).eval ((n : ℝ) + 1)
      = p.eval (n : ℝ) * q.eval ((n : ℝ) + 1) := by
    intro n; simp only [eval_mul, eval_comp, eval_sub, eval_X, eval_C]; ring_nf
  simp_rw [e2]
  have e3 : ∀ n : ℕ, p.eval (n : ℝ) * (q.eval ((n : ℝ) + 1) - q.eval (n : ℝ))
      = p.eval (n : ℝ) * q.eval ((n : ℝ) + 1) - p.eval (n : ℝ) * q.eval (n : ℝ) := by
    intro n; ring
  simp_rw [e3]
  rw [integral_sub hC hD]
  have e4 : ∀ n : ℕ, (p * q).eval (n : ℝ) = p.eval (n : ℝ) * q.eval (n : ℝ) := by
    intro n; simp only [eval_mul]
  simp_rw [e4]
  ring
end LevyStochCalc.Probability


