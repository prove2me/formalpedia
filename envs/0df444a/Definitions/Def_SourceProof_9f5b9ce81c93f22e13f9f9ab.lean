-- Prove2me | Definitions.Def_SourceProof_9f5b9ce81c93f22e13f9f9ab
-- name    : SourceProof_9f5b9ce81c93f22e13f9f9ab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:50:35.841529+00:00
-- url     : https://prove2.me/theorems/dd25701e-1e45-4cd6-aace-595f4b94e6fb
-- title:
--   LevyStochCalc source module: SourceProof_9f5b9ce81c93f22e13f9f9ab
-- statement:
--   The original source theorem `LevyStochCalc.Probability.sum_antidiagonal_div_factorial` comes from the `LevyStochCalc.Probability.HermiteGenerating` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Sum

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


theorem _root_.Prove2MeSourceProof.h_9f5b9ce81c93f22e13f9f9ab {K : Type*} [Field K] [CharZero K] (A B : K) (d : ℕ) :
    ∑ p ∈ antidiagonal d, A ^ p.1 * B ^ p.2 / ((p.1.factorial : K) * (p.2.factorial : K))
      = (A + B) ^ d / (d.factorial : K) := by
  rw [(Commute.all A B).add_pow' d, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hd : p.1 + p.2 = d := Finset.mem_antidiagonal.mp hp
  have h1 : (p.1.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr p.1.factorial_ne_zero
  have h2 : (p.2.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr p.2.factorial_ne_zero
  have h3 : (d.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
  have hc : ((d.choose p.1 : ℕ) : K) * ((p.1.factorial : K) * (p.2.factorial : K))
      = (d.factorial : K) := by
    rw [← hd]
    have h := Nat.add_choose_mul_factorial_mul_factorial p.2 p.1
    rw [add_comm p.2 p.1] at h
    have h' : ((p.1 + p.2).choose p.1 * (p.1.factorial * p.2.factorial) : ℕ)
        = (p.1 + p.2).factorial := by rw [← h]; ring
    exact_mod_cast congrArg (fun m : ℕ => (m : K)) h'
  rw [nsmul_eq_mul]
  field_simp
  linear_combination (-(A ^ p.1 * B ^ p.2)) * hc
end LevyStochCalc.Probability


