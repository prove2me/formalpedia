-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtRun
-- name    : ParetoNCSched_Supplement_rtRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:40:05.223207+00:00
-- url     : https://prove2.me/theorems/beab88f8-cfc7-4438-a85a-435573ea610d
-- title:
--   The run of $\mathrm{RT}_L$
-- statement:
--   The $k$-th state of the run of $\mathrm{RT}_L$ on sizes $p$ with predictions $y$: the $k$-fold iterate of one step from the state at time $0$, in which every elapsed time and the cost so far are $0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtStep

namespace ParetoNCSched.Supplement

/-- **The run of `RT_L`: the state after `k` steps.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13: all jobs start at
elapsed time `0` at time `0`.

**Formalization Note.** The `k`-th iterate of `rtStep` from `(0, 0, 0)`; constant once every job
has completed. -/
noncomputable def rtRun {n : ℕ} (L : ℝ) (p y : Fin n → ℝ) (k : ℕ) : MState n :=
  (rtStep L p y)^[k] ⟨0, 0, 0⟩

end ParetoNCSched.Supplement


