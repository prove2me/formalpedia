-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtNext
-- name    : ParetoNCSched_Supplement_rtNext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:36:32.91823+00:00
-- url     : https://prove2.me/theorems/9996e8b9-d8a2-4a58-a5c0-247c379df983
-- title:
--   The next job of the second stage of $\mathrm{RT}_L$
-- statement:
--   At a state of the run, the first unfinished job in the order of the predictions $y$, ties broken by index: the unfinished $i$ with $(y_i,i)$ lexicographically smallest. It is a single job when some job is unfinished.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, line 3, p.13; Appendix H, Notation, p.39

import Mathlib
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched.Supplement

open Classical in
/-- **The next job of the second stage.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, line 3, p.13: "run the unfinished jobs
alone, one at a time, in increasing order of yj", with "ties broken by index" (Appendix H,
Notation, p.39).

The set of unfinished jobs `i` that come first among the unfinished jobs in the order of
`(y_i, i)`: a singleton when some job is unfinished, empty otherwise. -/
noncomputable def rtNext {n : ℕ} (p y : Fin n → ℝ) (s : MState n) : Finset (Fin n) :=
  (unfinished p s).filter fun i => ∀ k ∈ unfinished p s, y i < y k ∨ (y i = y k ∧ i ≤ k)

end ParetoNCSched.Supplement


