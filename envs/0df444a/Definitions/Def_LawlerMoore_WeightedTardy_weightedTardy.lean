-- Prove2me | Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
-- name    : LawlerMoore_WeightedTardy_weightedTardy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:21.488076+00:00
-- url     : https://prove2.me/theorems/e79f2a0b-f497-410a-a3a6-07892f9a014f
-- title:
--   Section 5 — the weighted number of tardy jobs of a sequence
-- statement:
--   A set of $n$ jobs is processed by a single machine, one immediately following the other, starting at time $0$. Job $j$ requires $a'_j$ units of processing time and has a deadline $d_j$; both are nonnegative integers. If job $j$ completes at time $t$, it incurs the loss
--   $$
--   c_j(t) = \begin{cases} 0, & t \le d_j,\\ p_j, & t > d_j,\end{cases}
--   $$
--   that is, a penalty $p_j$ is exacted if job $j$ is completed later than its deadline. For a sequence $\sigma$ of the jobs, let $C_j(\sigma)$ be the completion time of job $j$ (the sum of the processing times of job $j$ and of the jobs before it). The **total loss**, or **weighted number of tardy jobs**, of $\sigma$ is
--   $$
--   W(\sigma) = \sum_{j \,:\, C_j(\sigma) > d_j} p_j .
--   $$
--
--   This is the objective of Section 5 of Lawler and Moore, which asks for a sequence minimizing it.
--
--   **Formalization Note** Jobs are `Fin n` (Lean job $j$ is the paper's job $j+1$). A sequence is a list `l`; the set of tardy jobs is the published `MooreLateJobs.NumLate.lateSet` (jobs of `l` with $d_j < C_j$), with completion times from the published `MooreLateJobs.Shared.completionTime` (no idle time, start at $0$). The list replaces the paper's permutation $\pi$; for a schedule (a duplicate-free list of all jobs) the completion time is the paper's $t_j = \sum_{k=1}^{\pi(j)} a'_{\pi^{-1}(k)}$. Processing times and deadlines are natural numbers, cast to $\mathbb R$; penalties are real.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 79, Section 5 (with the model of Section 4)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace LawlerMoore.WeightedTardy

/-- The total loss of §5 (Lawler–Moore 1969, p. 79): the weighted number of tardy jobs of the
sequence `l` of the jobs `Fin n` (Lean job `j` is the paper's job `j + 1`). Job `j` has the
integer processing time `a' j` and the integer deadline `d j`; it incurs the loss
`c_j(t) = 0` for `t ≤ d_j` and `c_j(t) = p_j` for `t > d_j`, where `t` is its completion time
when the jobs of `l` are processed one immediately following the other from time `0`. So the
total loss is the sum of `p j` over the jobs of `l` with `d j < C_j`, i.e. over the late set. -/
noncomputable def weightedTardy {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (l : List (Fin n)) : ℝ :=
  ∑ j ∈ MooreLateJobs.NumLate.lateSet (fun j => (a' j : ℝ)) (fun j => (d j : ℝ)) l, p j

end LawlerMoore.WeightedTardy


