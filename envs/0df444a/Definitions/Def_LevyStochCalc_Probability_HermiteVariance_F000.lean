-- Prove2me | Definitions.Def_LevyStochCalc_Probability_HermiteVariance_F000
-- name    : LevyStochCalc_Probability_HermiteVariance_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:30:59.203548+00:00
-- url     : https://prove2.me/theorems/5ae163bd-24e2-4497-9668-bf219d05ec6c
-- title:
--   Source declarations: LevyStochCalc.Probability.HermiteVariance
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.HermiteVariance. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The variance derivative of the Hermite polynomials

The Hermite polynomials `H_n(x; τ)` of variance `τ` satisfy the backward heat equation in the
variance, `∂_τ H_n(x; τ) + ½ ∂ₓ² H_n(x; τ) = 0`. Iterating the derivative rule
`H_(n+1)' = (n+1) H_n` gives `∂ₓ² H_(n+2) = (n+2)(n+1) H_n`, so the equation also reads
`∂_τ H_(n+2)(x; τ) = -((n+2)(n+1)/2) H_n(x; τ)`.

## Main statements

* `LevyStochCalc.Probability.derivative_two_hermitePoly` — `H_(n+2)'' = (n+2)(n+1) H_n`.
* `LevyStochCalc.Probability.derivative_two_hermitePoly_succ_succ` — the three-term recursion for
  the second derivatives.
* `LevyStochCalc.Probability.hasDerivAt_hermiteScaled` — `∂_τ H_n = -½ H_n''`.
* `LevyStochCalc.Probability.hasDerivAt_hermiteScaled_add_two` —
  `∂_τ H_(n+2) = -((n+2)(n+1)/2) H_n`.
-/

namespace LevyStochCalc.Probability

open Polynomial

/-- The second derivative of the Hermite polynomial of variance `τ`,
`H_(n+2)'' = (n+2)(n+1) H_n`. -/
theorem derivative_two_hermitePoly (τ : ℝ) (n : ℕ) :
    derivative (derivative (hermitePoly τ (n + 2)))
      = C (((n : ℝ) + 2) * ((n : ℝ) + 1)) * hermitePoly τ n := by
  have h1 : derivative (hermitePoly τ (n + 1 + 1))
      = C (((n : ℕ) + 1 : ℝ) + 1) * hermitePoly τ (n + 1) := by
    simpa using derivative_hermitePoly τ (n + 1)
  rw [show n + 2 = n + 1 + 1 from rfl, h1, derivative_C_mul, derivative_hermitePoly τ n,
    ← mul_assoc, ← C_mul,
    show ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) = ((n : ℝ) + 2) * ((n : ℝ) + 1) from by ring]
/-- The three-term recursion satisfied by the second derivatives of the Hermite polynomials of
variance `τ`. -/
theorem derivative_two_hermitePoly_succ_succ (τ : ℝ) (n : ℕ) :
    derivative (derivative (hermitePoly τ (n + 2)))
      = X * derivative (derivative (hermitePoly τ (n + 1)))
        + 2 * derivative (hermitePoly τ (n + 1))
        - C (((n : ℝ) + 1) * τ) * derivative (derivative (hermitePoly τ n)) := by
  rw [hermitePoly_succ_succ τ n]
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, one_mul, zero_mul,
    zero_add, derivative_add]
  ring
/-- The backward heat equation in the variance for the Hermite polynomials,
`∂_τ H_n(x; τ) + ½ ∂ₓ² H_n(x; τ) = 0`. -/
theorem hasDerivAt_hermiteScaled (n : ℕ) (x τ : ℝ) :
    HasDerivAt (fun t => hermiteScaled n t x)
      (-(1 / 2) * (derivative (derivative (hermitePoly τ n))).eval x) τ := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hasDerivAt_const τ (1 : ℝ)
  | one => simpa using hasDerivAt_const τ x
  | more n ih1 ih2 =>
    have h2 : HasDerivAt (fun t : ℝ => ((n : ℝ) + 1) * t) ((n : ℝ) + 1) τ := by
      simpa using (hasDerivAt_id τ).const_mul ((n : ℝ) + 1)
    have hmain : HasDerivAt
        (fun t => x * hermiteScaled (n + 1) t x - ((n : ℝ) + 1) * t * hermiteScaled n t x)
        (x * (-(1 / 2) * (derivative (derivative (hermitePoly τ (n + 1)))).eval x)
          - (((n : ℝ) + 1) * hermiteScaled n τ x
            + ((n : ℝ) + 1) * τ * (-(1 / 2) * (derivative (derivative (hermitePoly τ n))).eval x)))
        τ := (ih2.const_mul x).sub (h2.mul ih1)
    have hfun : (fun t => hermiteScaled (n + 2) t x)
        = fun t => x * hermiteScaled (n + 1) t x - ((n : ℝ) + 1) * t * hermiteScaled n t x := by
      funext t; rw [hermiteScaled_succ_succ]
    have hD := congrArg (fun p : ℝ[X] => p.eval x) (derivative_two_hermitePoly_succ_succ τ n)
    have hd1 : (derivative (hermitePoly τ (n + 1))).eval x
        = ((n : ℝ) + 1) * hermiteScaled n τ x := by
      rw [derivative_hermitePoly τ n]
      simp [hermiteScaled]
    simp only [eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_ofNat] at hD
    rw [hd1] at hD
    rw [hfun, hD]
    convert hmain using 1
    ring
/-- The backward heat equation in the variance in shifted form,
`∂_τ H_(n+2)(x; τ) = -((n+2)(n+1)/2) H_n(x; τ)`. -/
theorem hasDerivAt_hermiteScaled_add_two (n : ℕ) (x τ : ℝ) :
    HasDerivAt (fun t => hermiteScaled (n + 2) t x)
      (-((((n : ℝ) + 2) * ((n : ℝ) + 1)) / 2) * hermiteScaled n τ x) τ := by
  have h := hasDerivAt_hermiteScaled (n + 2) x τ
  rw [derivative_two_hermitePoly] at h
  have he : (C (((n : ℝ) + 2) * ((n : ℝ) + 1)) * hermitePoly τ n).eval x
      = ((n : ℝ) + 2) * ((n : ℝ) + 1) * hermiteScaled n τ x := by
    simp [hermiteScaled]
  rw [he] at h
  convert h using 1
  ring
end LevyStochCalc.Probability


