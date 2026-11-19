-- Prove2me | Definitions.Def_SourceProof_2ee02b5cd77c741d226b69cf
-- name    : SourceProof_2ee02b5cd77c741d226b69cf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:07:40.104463+00:00
-- url     : https://prove2.me/theorems/9bfc6dc9-49c7-4508-98a9-ff05aff25bfa
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.integral_mul_eval_poissonMeasure
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F000

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


theorem _root_.Prove2MeSourceProof.h_2ee02b5cd77c741d226b69cf (r : ℝ≥0) (p : ℝ[X]) :
    ∫ n : ℕ, (n : ℝ) * p.eval (n : ℝ) ∂poissonMeasure r
      = (r : ℝ) * ∫ n : ℕ, p.eval ((n : ℝ) + 1) ∂poissonMeasure r := by
  have hsum : Summable
      (fun n : ℕ => (Real.exp (-r) * (r : ℝ) ^ n / n !) • ((n : ℝ) * p.eval (n : ℝ))) := by
    have h := LevyStochCalc.Probability.integrable_eval_poissonMeasure r (X * p)
    simp only [eval_mul, eval_X] at h
    have := integrable_poissonMeasure_iff.1 h
    refine Summable.of_norm ?_
    refine this.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    rw [smul_eq_mul, norm_mul, Real.norm_eq_abs (Real.exp (-r) * (r : ℝ) ^ n / n !),
      abs_of_nonneg (by positivity)]
  rw [integral_poissonMeasure, integral_poissonMeasure, hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, smul_eq_mul, mul_zero, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hfac : ((m + 1)! : ℝ) = ((m : ℝ) + 1) * m ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  push_cast [hfac]
  have h0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h1 : ((m ! : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring
end LevyStochCalc.Probability


