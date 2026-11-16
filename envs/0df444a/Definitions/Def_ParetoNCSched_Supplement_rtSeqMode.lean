-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtSeqMode
-- name    : ParetoNCSched_Supplement_rtSeqMode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:35:45.278625+00:00
-- url     : https://prove2.me/theorems/42c03c34-fde0-412c-aa72-5b7002cfbe5a
-- title:
--   The second stage of $\mathrm{RT}_L$
-- statement:
--   $\mathrm{RT}_L$ runs Round-Robin until the common elapsed time of the unfinished jobs reaches $L$, then the unfinished jobs one at a time in increasing order of $y_j$, and from the first mismatch Round-Robin on the unfinished jobs of smallest elapsed time. The run is in its **second stage** at a state when no mismatch has occurred and every unfinished job has elapsed time at least $L$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13; Appendix H, p.40

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtMismatch
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched.Supplement

/-- **`RT_L` is in its second stage.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, lines 2–4, p.13: "run Round-Robin until
the common elapsed time of the unfinished jobs reaches L; run the unfinished jobs alone, one at a
time, in increasing order of yj; at the first mismatch, if any, run Round-Robin on the unfinished
jobs of smallest elapsed time until all jobs complete".

The second stage is on when no mismatch has occurred and every unfinished job has elapsed time at
least `L` (the first stage, in which the unfinished jobs share one elapsed time, is over). -/
def rtSeqMode {n : ℕ} (L : ℝ) (p y : Fin n → ℝ) (s : MState n) : Prop :=
  ¬ rtMismatch p y s ∧ ∀ i ∈ unfinished p s, L ≤ s.e i

end ParetoNCSched.Supplement


