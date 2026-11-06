-- Prove2me | Definitions.Def_ParetoNCSched_mrcRate
-- name    : ParetoNCSched_mrcRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:19:15.076666+00:00
-- url     : https://prove2.me/theorems/36357f23-3866-439a-bde6-0dfee81763ef
-- title:
--   The rate function of $\mathrm{MRC}_R$
-- statement:
--   The rate function of $\mathrm{MRC}_R$: on each interval $[t_k,t_{k+1})$ it uses the rates computed at $t_k$,
--   $$r(t)=\sum_{k\ge0}\mathbf 1\big[t\in[t_k,t_{k+1})\big]\, r^{(k)} .$$
--   Outside these intervals (before time $0$, and after the run if it never ends) the rates are $0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, p.9; Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_eventTime
import Definitions.Def_ParetoNCSched_stepRates

namespace ParetoNCSched

/-- **The rate function of `MRC_R`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, p.9, and Appendix B, p.17: on each interval
`[t_k, t_{k+1})` the rates computed at `t_k` are used ("All rates are constant between consecutive
events", p.9).

**Formalization Note.** `r(t) = Σ_k 1[t ∈ [t_k, t_{k+1})] · r_k`, where `r_k = stepRates` of the
`k`-th state. The intervals are disjoint because the event times are non-decreasing, so at most one
term is non-zero. Outside `⋃ₖ [t_k, t_{k+1})` (before time `0`, and after the run if it never
ends) the rate is `0`. -/
noncomputable def mrcRate {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ℝ → Fin n → ℝ :=
  fun t i => ∑' k : ℕ, (Set.Ico (eventTime R p σ k) (eventTime R p σ (k + 1))).indicator
    (fun _ => stepRates R p σ (run R p σ k) i) t

end ParetoNCSched


