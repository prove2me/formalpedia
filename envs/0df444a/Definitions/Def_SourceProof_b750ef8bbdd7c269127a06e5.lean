-- Prove2me | Definitions.Def_SourceProof_b750ef8bbdd7c269127a06e5
-- name    : SourceProof_b750ef8bbdd7c269127a06e5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T16:59:52.248993+00:00
-- url     : https://prove2.me/theorems/98d08d56-9299-4137-bce9-ca7edaa4040d
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.summable_sqrt_pow_div_factorial
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Series of square integrable complex functions with summable `L²` norms

For a series `∑_r f_r` of square integrable complex functions on a probability space whose `L²`
norms `‖f_r‖_(L²) = (E‖f_r‖ ^ 2) ^ (1/2)` are summable, the series of the classes converges in
`L²(P)` because `Lp ℂ 2 P` is complete and absolute summability implies summability there. If the
series also sums pointwise almost everywhere to a function `g`, the two limits agree: the partial
sums converge to the `L²` limit in measure and converge to `g` almost everywhere, hence in
measure, and limits in measure are almost everywhere unique. Consequently `g` is itself square
integrable and the series of the classes converges in `L²(P)` to the class of `g`, so square
integrability of the sum is a conclusion of the criterion rather than a hypothesis. If moreover
the terms are pairwise orthogonal, `E‖f_r‖ ^ 2` sums to `E‖g‖ ^ 2`.

The scalar criterion `∑_r (x ^ r / r!) ^ (1/2) < ∞` for `0 ≤ x` is what makes the criterion
applicable to the series whose `L²` norms are those of the exponential series, and follows from
`(u w) ^ (1/2) ≤ (u + w) / 2` at `u = (2x) ^ r / r!` and `w = 2 ^ (-r)`.

## Main statements

* `LevyStochCalc.Probability.norm_toLp_sq` — `‖[f]‖ ^ 2 = E‖f‖ ^ 2`.
* `LevyStochCalc.Probability.inner_toLp` — `⟪[f], [g]⟫ = E[conj f · g]`.
* `LevyStochCalc.Probability.coeFn_sum_range` — the class of a finite sum is the pointwise sum.
* `LevyStochCalc.Probability.summable_sqrt_pow_div_factorial` —
  `∑_r (x ^ r / r!) ^ (1/2) < ∞` for `0 ≤ x`.
* `LevyStochCalc.Probability.hasSum_norm_sq_of_hasSum` — Parseval for a pairwise orthogonal
  series in `L²`.
* `LevyStochCalc.Probability.hasSum_integral_norm_sq_of_hasSum_toLp` — the same in terms of
  second moments.
* `LevyStochCalc.Probability.summable_toLp` — summability in `L²` from summable `L²` norms.
* `LevyStochCalc.Probability.coeFn_tsum_toLp` — the `L²` sum agrees almost everywhere with the
  almost everywhere pointwise sum.
* `LevyStochCalc.Probability.memLp_two_of_hasSum_ae` — the almost everywhere pointwise sum is
  square integrable.
* `LevyStochCalc.Probability.hasSum_toLp_of_summable_norm` — the series converges in `L²(P)` to
  its almost everywhere pointwise sum.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_b750ef8bbdd7c269127a06e5 {x : ℝ} (hx : 0 ≤ x) :
    Summable fun r : ℕ => Real.sqrt (x ^ r / (r.factorial : ℝ)) := by
  have hb : Summable fun r : ℕ => ((2 * x) ^ r / (r.factorial : ℝ) + (1 / 2 : ℝ) ^ r) / 2 :=
    (((Real.summable_pow_div_factorial (2 * x)).add
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))).div_const 2)
  refine Summable.of_nonneg_of_le (fun r => Real.sqrt_nonneg _) (fun r => ?_) hb
  have hr : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  have hkey : x ^ r / (r.factorial : ℝ)
      = ((2 * x) ^ r / (r.factorial : ℝ)) * ((1 / 2 : ℝ) ^ r) := by
    rw [mul_pow, div_pow]
    field_simp
    ring
  rw [hkey]
  calc Real.sqrt (((2 * x) ^ r / (r.factorial : ℝ)) * ((1 / 2 : ℝ) ^ r))
      ≤ Real.sqrt ((((2 * x) ^ r / (r.factorial : ℝ) + (1 / 2 : ℝ) ^ r) / 2) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [sq_nonneg ((2 * x) ^ r / (r.factorial : ℝ) - (1 / 2 : ℝ) ^ r)]
    _ = ((2 * x) ^ r / (r.factorial : ℝ) + (1 / 2 : ℝ) ^ r) / 2 :=
        Real.sqrt_sq (by positivity)
section Series

variable [IsProbabilityMeasure P] {f : ℕ → Ω → ℂ} {g : Ω → ℂ}

end Series

end LevyStochCalc.Probability


