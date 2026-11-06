-- Prove2me | Definitions.Def_ParetoNCSched_eventTime
-- name    : ParetoNCSched_eventTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:17:22.869346+00:00
-- url     : https://prove2.me/theorems/287c997a-045b-4d19-b143-bbbce3e57d5f
-- title:
--   Event times $t_k$ of the run of $\mathrm{MRC}_R$
-- statement:
--   The time $t_k$ of the $k$-th state of the run. While at least two jobs are unfinished these are the event times of the paper; the index after the state with one unfinished job is the time of the final completion, and the times are constant afterwards.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_run

namespace ParetoNCSched

/-- **The event times `t_k`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17.

**Formalization Note.** `eventTime R p σ k` is the time of the `k`-th state of the run. While
`N ≥ 2` these are the paper's event times; the index after the state with `N = 1` is the final
completion time (which the paper does not count as an event), and the times are constant
afterwards. -/
noncomputable def eventTime {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℝ :=
  (run R p σ k).time

end ParetoNCSched


