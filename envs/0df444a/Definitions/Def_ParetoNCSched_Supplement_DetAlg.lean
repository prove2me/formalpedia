-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_DetAlg
-- name    : ParetoNCSched_Supplement_DetAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:25:59.252149+00:00
-- url     : https://prove2.me/theorems/e8a3e17e-3612-4b26-8a7a-b3ca39fc3ed0
-- title:
--   Deterministic algorithms: rate functions of the completion history
-- statement:
--   A **deterministic algorithm** in a prediction model knows the number $n$ of jobs and the prediction $y$, and at any time knows which jobs have completed and when, but not the sizes. Formally it assigns to every $n$, every prediction $y$ and every completion history $H=((j_1,C_1),\dots,(j_k,C_k))$ (with $C_1\le\dots\le C_k$, simultaneous completions listed by index, $C_0=0$) a measurable rate function $r^{H}$ on $[C_k,\infty)$ with
--
--   $$r^H_j(t)\ge0,\qquad \sum_j r^H_j(t)\le1,\qquad r^H_j\equiv0\ \text{for } j\in H.$$
--
--   No non-idling, piecewise-constancy or finiteness condition is imposed; an algorithm may leave a job unprocessed forever.
--
--   **Formalization Note** The rate function is a function of all real times and is defined for every list of (job, time) pairs; only its values on $[C_k,\infty)$ at the histories of a run are used. The three conditions are required everywhere; every rate function of the paper extends by $0$ to one that satisfies them, so the class of runs is the paper's.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15; Appendix E, Predicted sizes, p.31

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_PredModel
import Definitions.Def_ParetoNCSched_IsSchedule

namespace ParetoNCSched.Supplement

/-- **Deterministic algorithm.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15: "A deterministic algorithm knows n
and σ, and at any time knows which jobs have completed and when. Formally, it assigns to every
completion history H = ((j1, C1), . . . , (jk, Ck)), with C1 ≤ ⋯ ≤ Ck (simultaneous completions
listed by index; C0 := 0 for the empty history), a measurable rate function on [Ck, ∞), with
non-negative rates summing to at most 1 and supported on the jobs not in H." Appendix E, p.31:
the same definition with predicted sizes `y` in place of `σ`.

`rate n y H t j` is the rate the algorithm gives job `j` at time `t` when it has `n` jobs,
prediction `y`, and completion history `H` (a list of pairs (job, completion time)).

**Formalization Note.**
* The algorithm is a family over all `n`, and it sees only `n`, the prediction and the history,
  never the sizes `p`. No non-idling, piecewise-constancy or finiteness condition is imposed.
* The rate function is a function on all of `ℝ` and is defined for every list of pairs, also
  for lists that are not histories of any run; only its values on `[C_k, ∞)` at the histories of
  the run are ever used (`curRate`). The conditions (`IsSchedule`: measurable, non-negative,
  summing to at most `1`; zero on the jobs of `H`) are required everywhere. Every rate function
  on `[C_k, ∞)` of the paper extends by `0` to one satisfying them, so the runs are the
  paper's. -/
structure DetAlg (M : PredModel) where
  /-- the rate function assigned to `n`, a prediction and a completion history -/
  rate : (n : ℕ) → M.Pred n → List (Fin n × ℝ) → ℝ → Fin n → ℝ
  /-- measurable, non-negative rates summing to at most `1` -/
  isSchedule : ∀ n y H, IsSchedule (rate n y H)
  /-- supported on the jobs not in the history -/
  support : ∀ n y H t j, j ∈ H.map Prod.fst → rate n y H t j = 0

end ParetoNCSched.Supplement


