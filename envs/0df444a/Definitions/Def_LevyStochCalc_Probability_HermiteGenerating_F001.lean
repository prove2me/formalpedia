-- Prove2me | Definitions.Def_LevyStochCalc_Probability_HermiteGenerating_F001
-- name    : LevyStochCalc_Probability_HermiteGenerating_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:32:01.295184+00:00
-- url     : https://prove2.me/theorems/3d5ae0cd-f001-49db-a02f-4a1fa2db7c6a
-- title:
--   Source declarations: LevyStochCalc.Probability.HermiteGenerating
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.HermiteGenerating. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_HermiteGenerating_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Hermite polynomials of variance `τ`

The Hermite polynomials of variance `τ` are generated over `ℂ` by
`e^(t x - t ^ 2 τ / 2) = ∑_r (t ^ r / r!) H_r(x; τ)`, which follows from the Appell binomial
decomposition `H_n(x; τ) / n! = ∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)` by an antidiagonal
Cauchy product of the exponential series with the series of the values at the origin, the latter
summing to `e^(-t ^ 2 τ / 2)` because `H_(2b)(0; τ) = (-τ / 2) ^ b (2b)! / b!` and
`H_(2b+1)(0; τ) = 0`. A complex scalar covers the purely imaginary frequencies `t = i a`, where
the identity reads `e^(i a x + a ^ 2 τ / 2) = ∑_r ((i a) ^ r / r!) H_r(x; τ)`. Both factors of
the Cauchy product are absolutely summable, hence so is the scaled Hermite series itself, at
every argument and every complex scalar.

## Main statements

* `LevyStochCalc.Probability.hermiteScaled_two_mul_zero` —
  `H_(2b)(0; τ) = (-τ / 2) ^ b (2b)! / b!`.
* `LevyStochCalc.Probability.hermiteScaled_two_mul_add_one_zero` — `H_(2b+1)(0; τ) = 0`.
* `LevyStochCalc.Probability.sum_antidiagonal_hermiteScaled` — the Appell binomial identity
  `H_n(x; τ) / n! = ∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)`.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_zero` —
  `e^(-t ^ 2 τ / 2) = ∑_m (t ^ m / m!) H_m(0; τ)`.
* `LevyStochCalc.Probability.hasSum_hermiteScaled` —
  `e^(t x - t ^ 2 τ / 2) = ∑_r (t ^ r / r!) H_r(x; τ)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_expTerm` — absolute summability of `z ^ a / a!`.
* `LevyStochCalc.Probability.summable_norm_hermiteScaled_zero` — absolute summability of
  `t ^ m / m! · H_m(0; τ)`.
* `LevyStochCalc.Probability.summable_norm_hermiteScaled` — absolute summability of
  `t ^ r / r! · H_r(x; τ)` at every argument.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_real` — the same identity for a real scalar.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_I` —
  `e^(i a x + a ^ 2 τ / 2) = ∑_r ((i a) ^ r / r!) H_r(x; τ)`.
* `LevyStochCalc.Probability.sum_antidiagonal_div_factorial` —
  `∑_(r + s = d) A ^ r B ^ s / (r! s!) = (A + B) ^ d / d!`.
-/

namespace LevyStochCalc.Probability

open Finset

/-- The Hermite generating function over `ℝ`. -/
theorem hasSum_hermiteScaled_real (τ x t : ℝ) :
    HasSum (fun r : ℕ => t ^ r / (r.factorial : ℝ) * hermiteScaled r τ x)
      (Real.exp (t * x - t ^ 2 * τ / 2)) := by
  have h := (hasSum_hermiteScaled τ x (t : ℂ)).mapL Complex.reCLM
  have hf : ∀ r : ℕ, Complex.reCLM ((t : ℂ) ^ r / (r.factorial : ℂ)
      * (hermiteScaled r τ x : ℂ)) = t ^ r / (r.factorial : ℝ) * hermiteScaled r τ x := by
    intro r
    have : ((t : ℂ) ^ r / (r.factorial : ℂ) * (hermiteScaled r τ x : ℂ))
        = ((t ^ r / (r.factorial : ℝ) * hermiteScaled r τ x : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.reCLM_apply, Complex.ofReal_re]
  have hg : Complex.reCLM (Complex.exp ((t : ℂ) * x - (t : ℂ) ^ 2 * τ / 2))
      = Real.exp (t * x - t ^ 2 * τ / 2) := by
    have : ((t : ℂ) * x - (t : ℂ) ^ 2 * τ / 2)
        = ((t * x - t ^ 2 * τ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_exp, Complex.reCLM_apply, Complex.ofReal_re]
  rw [funext hf, hg] at h
  exact h
/-- The Hermite expansion of a complex exponential of purely imaginary frequency,
`e^(i a x + a² τ / 2) = ∑_r ((i a)^r / r!) H_r(x; τ)`. -/
theorem hasSum_hermiteScaled_I (τ x a : ℝ) :
    HasSum (fun r : ℕ => (Complex.I * a) ^ r / (r.factorial : ℂ) * (hermiteScaled r τ x : ℂ))
      (Complex.exp (Complex.I * a * x + a ^ 2 * τ / 2)) := by
  have h := hasSum_hermiteScaled τ x (Complex.I * a)
  have he : Complex.I * (a : ℂ) * x - (Complex.I * a) ^ 2 * τ / 2
      = Complex.I * a * x + (a : ℂ) ^ 2 * τ / 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [he] at h
  exact h
end LevyStochCalc.Probability


