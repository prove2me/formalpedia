-- Prove2me | Definitions.Def_TwoAgentSched_TotalMax_Rules
-- name    : TwoAgentSched_TotalMax_Rules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:42:13.454259+00:00
-- url     : https://prove2.me/theorems/10ff4e11-09d0-4bb9-992e-4dc10a7dae46
-- title:
--   Figure 1 and §5.2.1: the backward rule (eligible B-job, else longest A-job) and its least-cost variant, as properties of a finished sequence
-- statement:
--   The two algorithms of §5.2 of Agnetis et al. (2004), described by the sequences they can produce.
--
--   Both build the schedule backwards, from the last position to the first. When a position is filled, let $U$ be the set of jobs not yet scheduled and $\tau$ the sum of their processing times, which is the completion time of the job placed in this position.
--
--   **Algorithm of Figure 1.** If some unscheduled $B$-job $J^B_k$ satisfies $f^B_k(\tau)\le Q$, place such a job (any of them) last. Otherwise place last a longest unscheduled $A$-job, i.e. an $A$-job $J^A_h\in U$ with $p^A_{h'}\le p^A_h$ for every $A$-job $J^A_{h'}\in U$ (any of them, if several are longest). If no $B$-job qualifies and no $A$-job is left, the algorithm stops: "no solution exists".
--
--   **Modified algorithm of §5.2.1.** The same, except that when some unscheduled $B$-job satisfies $f^B_k(\tau)\le Q$, the job placed last is a $B$-job $J^B_l$ with
--   $$f^B_l(\tau)=\min_{k\in U^B} f^B_k(\tau),$$
--   where $U^B$ is the set of all unscheduled $B$-jobs. Ties are broken arbitrarily. The schedule it produces is called $\tilde\sigma$ in the paper.
--
--   A sequence of all jobs satisfies the rule if at every position the job there is a choice the rule allows; a stop leaves no allowed choice, so a complete sequence satisfying the rule is exactly a run of the algorithm that does not stop.
--
--   **Formalization Note** Position $m$ (0-based) of the list $l$ is filled when the unscheduled jobs are $l[0],\dots,l[m]$, and $\tau$ is the completion time at position $m$. Ties are quantified universally: the rule constrains $l[m]$ but not which of several allowed jobs it is. The minimum in the modified rule is taken over all unscheduled $B$-jobs, as printed; that minimum is then automatically at most $Q$, so every sequence of the modified rule also satisfies the rule of Figure 1.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, Figure 1 and the paragraph before Theorem 5.5; p. 235, §5.2.1 (the modified algorithm)

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Model

namespace TwoAgentSched.TotalMax

/-- The sequence `l` can be produced by the algorithm of Figure 1 (§5.2, p. 234), with ties
broken arbitrarily. The algorithm fills the positions from last to first; when the (0-based)
position `m` is filled, the unscheduled jobs are `U = {l[0], …, l[m]}`, and the job placed there
ends at `τ = completionAt p l m`, the sum of the processing times of the jobs of `U`. For every
position `m`:
1. if some unscheduled B-job `k ∈ U` has `f^B_k(τ) ≤ Q`, then `l[m]` is such a B-job (any of
   them);
2. otherwise, `l[m]` is a longest unscheduled A-job: an A-job `h ∈ U` with `p_{h'} ≤ p_h` for
   every A-job `h' ∈ U` (any of them, if several are longest).
The algorithm stops ("no solution exists") when case 1 does not apply and `U` holds no A-job;
such a position admits no choice of `l[m]`, so no sequence through it satisfies this property. -/
def IsFig1Seq {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (TwoAgentSched.MaxMax.Job nA nB)) : Prop :=
  ∀ (m : ℕ) (hm : m < l.length),
    ((∃ k : Fin nB, Sum.inr k ∈ (l.take (m + 1)).toFinset ∧
        fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) →
      ∃ k : Fin nB, l[m] = Sum.inr k ∧ fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) ∧
    ((¬ ∃ k : Fin nB, Sum.inr k ∈ (l.take (m + 1)).toFinset ∧
        fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) →
      ∃ h : Fin nA, l[m] = Sum.inl h ∧
        ∀ h' : Fin nA, Sum.inl h' ∈ (l.take (m + 1)).toFinset → p (Sum.inl h') ≤ p (Sum.inl h))

/-- The sequence `l` can be produced by the modified algorithm of §5.2.1 (p. 235), with ties
broken arbitrarily: the algorithm of Figure 1, except that whenever some unscheduled B-job `k`
has `f^B_k(τ̄) ≤ Q`, it schedules last the B-job `J^B_l` with
`f^B_l(τ̄) = min_{k ∈ U^B} f^B_k(τ̄)`, the minimum taken over all unscheduled B-jobs `U^B`.
With `U = {l[0], …, l[m]}` and `τ̄ = completionAt p l m`, for every position `m`:
1. if some B-job `k ∈ U` has `f^B_k(τ̄) ≤ Q`, then `l[m]` is a B-job `k₀ ∈ U` with
   `f^B_{k₀}(τ̄) ≤ f^B_{k'}(τ̄)` for every B-job `k' ∈ U`;
2. otherwise, `l[m]` is a longest A-job of `U`, as in Figure 1. -/
def IsLeastCostSeq {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (TwoAgentSched.MaxMax.Job nA nB)) : Prop :=
  ∀ (m : ℕ) (hm : m < l.length),
    ((∃ k : Fin nB, Sum.inr k ∈ (l.take (m + 1)).toFinset ∧
        fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) →
      ∃ k : Fin nB, l[m] = Sum.inr k ∧
        ∀ k' : Fin nB, Sum.inr k' ∈ (l.take (m + 1)).toFinset →
          fB k (MooreLateJobs.Shared.completionAt p l m) ≤
            fB k' (MooreLateJobs.Shared.completionAt p l m)) ∧
    ((¬ ∃ k : Fin nB, Sum.inr k ∈ (l.take (m + 1)).toFinset ∧
        fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) →
      ∃ h : Fin nA, l[m] = Sum.inl h ∧
        ∀ h' : Fin nA, Sum.inl h' ∈ (l.take (m + 1)).toFinset → p (Sum.inl h') ≤ p (Sum.inl h))

end TwoAgentSched.TotalMax


