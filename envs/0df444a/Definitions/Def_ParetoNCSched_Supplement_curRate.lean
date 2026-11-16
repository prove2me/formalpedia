-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_curRate
-- name    : ParetoNCSched_Supplement_curRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:26:56.053054+00:00
-- url     : https://prove2.me/theorems/0eb5d815-c5fc-4da2-8d90-abb051397016
-- title:
--   The rate function followed from a state of the run
-- statement:
--   From the state after the $k$-th completion, the run follows the rate function
--
--   $$r(t)=\begin{cases} r^{\mathrm{run}}(t), & t<C_k,\\ r^{H_k}(t), & t\ge C_k,\end{cases}$$
--
--   that is, the run so far before $C_k$ and, from $C_k$ on, the rate function the algorithm assigns to the current history, until the next completion.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_DetAlg
import Definitions.Def_ParetoNCSched_Supplement_AlgRunState

namespace ParetoNCSched.Supplement

/-- **The rate function followed from a state.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15: "after the k-th
completion, the algorithm follows the rate function of the current history until the next
completion."

From the state after the `k`-th completion: before `C_k` the run's rate function so far, from
`C_k` on the rate function the algorithm assigns to the current history. -/
noncomputable def curRate {M : PredModel} (A : DetAlg M) {n : ℕ} (y : M.Pred n)
    (s : AlgRunState n) : ℝ → Fin n → ℝ :=
  fun t => if t < s.last then s.rate t else A.rate n y s.hist t

end ParetoNCSched.Supplement


