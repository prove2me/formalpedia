-- Prove2me | Definitions.Def_LevyStochCalc_Probability_L2Series_F000
-- name    : LevyStochCalc_Probability_L2Series_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:35:21.341305+00:00
-- url     : https://prove2.me/theorems/ff026f69-47bb-4afa-96d2-993730fbf968
-- title:
--   Source declarations: LevyStochCalc.Probability.L2Series
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.L2Series. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_a136dbb94044eec9a3219314
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

/-- The `L²` norm of the class of a square integrable function is the square root of the second
moment of its modulus. -/
theorem norm_toLp (f : Ω → ℂ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ = Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂P) := by
  rw [← _root_.Prove2MeSourceProof.h_a136dbb94044eec9a3219314 f hf, Real.sqrt_sq (norm_nonneg _)]
/-- The `L²` pairing of the classes of two square integrable functions. -/
theorem inner_toLp (f g : Ω → ℂ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ ω, (starRingEnd ℂ) (f ω) * g ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [RCLike.inner_apply, h1, h2]
  ring
/-- A finite sum of classes of square integrable functions is the class of the pointwise sum. -/
theorem coeFn_sum_range (F : ℕ → Lp ℂ 2 P) (n : ℕ) :
    ((∑ r ∈ Finset.range n, F r : Lp ℂ 2 P) : Ω → ℂ)
      =ᵐ[P] fun ω => ∑ r ∈ Finset.range n, (F r : Ω → ℂ) ω := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 P
  | succ n ih =>
    rw [Finset.sum_range_succ]
    filter_upwards [Lp.coeFn_add (∑ r ∈ Finset.range n, F r) (F n), ih] with ω h1 h2
    rw [h1, Finset.sum_range_succ]
    simp only [Pi.add_apply]
    rw [h2]
section Series

variable [IsProbabilityMeasure P] {f : ℕ → Ω → ℂ} {g : Ω → ℂ}

end Series

end LevyStochCalc.Probability


