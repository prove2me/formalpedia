-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_nextCands
-- name    : ParetoNCSched_Supplement_nextCands
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:27:39.044208+00:00
-- url     : https://prove2.me/theorems/edde58c5-d33d-47c8-9760-dcc08f5587ac
-- title:
--   Candidate times of the next completion
-- statement:
--   From the state after the $k$-th completion, the candidate times of the next completion are the times $t\ge C_k$ at which some job $j$ not in the history has elapsed time $e_j(t)=\int_0^t r_j(u)\,du\ge p_j$ under the rate function followed from the state. The next completion time is the infimum of this set.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15; Section 2, p.7

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_curRate
import Definitions.Def_ParetoNCSched_elapsed

namespace ParetoNCSched.Supplement

/-- **Candidate times of the next completion.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15 ("until the next
completion"), with Section 2, p.7: job `j` completes when `e_j` reaches `p_j`.

The times `t ≥ C_k` at which some job not in the history has elapsed time at least its size,
under the rate function followed from the state. The next completion time is the infimum of this
set (`algStep`). -/
noncomputable def nextCands {M : PredModel} (A : DetAlg M) {n : ℕ} (p : Fin n → ℝ)
    (y : M.Pred n) (s : AlgRunState n) : Set ℝ :=
  {t | s.last ≤ t ∧ ∃ j, j ∉ s.hist.map Prod.fst ∧ p j ≤ elapsed (curRate A y s) j t}

end ParetoNCSched.Supplement


