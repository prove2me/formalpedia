-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtRate
-- name    : ParetoNCSched_Supplement_rtRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:41:04.145305+00:00
-- url     : https://prove2.me/theorems/29d60107-da14-4157-9c9e-20571f18cb06
-- title:
--   The rate function of $\mathrm{RT}_L$
-- statement:
--   The rate function of the run of $\mathrm{RT}_L$: on each interval $[t_k,t_{k+1})$ between the times of consecutive states, the rates of the $k$-th state; $0$ outside the union of these intervals.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtRun

namespace ParetoNCSched.Supplement

/-- **The rate function of `RT_L`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13: on each interval `[t_k, t_{k+1})`
between consecutive states of the run, the rates of the `k`-th state are used.

**Formalization Note.** `r(t) = Σ_k 1[t ∈ [t_k, t_{k+1})] r_k` with `r_k = rtRates` at the `k`-th
state, as for the base mission's `mrcRate`. The times are non-decreasing, so at most one term is
non-zero; outside the union of the intervals the rate is `0`. -/
noncomputable def rtRate {n : ℕ} (L : ℝ) (p y : Fin n → ℝ) : ℝ → Fin n → ℝ :=
  fun t i => ∑' k : ℕ, (Set.Ico (rtRun L p y k).time (rtRun L p y (k + 1)).time).indicator
    (fun _ => rtRates L p y (rtRun L p y k) i) t

end ParetoNCSched.Supplement


