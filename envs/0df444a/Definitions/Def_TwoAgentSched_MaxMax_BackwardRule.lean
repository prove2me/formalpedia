-- Prove2me | Definitions.Def_TwoAgentSched_MaxMax_BackwardRule
-- name    : TwoAgentSched_MaxMax_BackwardRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:48.367984+00:00
-- url     : https://prove2.me/theorems/abcf8587-4336-43ab-9a73-982e9dc3bd93
-- title:
--   §4: sequences produced by the backward rule — place last an eligible B-job, else an A-job of least cost
-- statement:
--   The algorithm of §4 for $1\|f^A_{\max} : f^B_{\max}\le Q$ builds the schedule from the end. At each step it chooses, among the unscheduled jobs, the job to be scheduled last. Let $U$ be the set of unscheduled jobs and $\bar\tau=\sum_{j\in U}p_j$, the time at which the chosen job ends. Then
--
--   1. if some unscheduled B-job $J^B_k$ has $f^B_k(\bar\tau)\le Q$, any such B-job is scheduled to end at $\bar\tau$;
--   2. if there is no such B-job, an unscheduled A-job $J^A_h$ with the smallest value $f^A_h(\bar\tau)$ among the unscheduled A-jobs is scheduled to end at $\bar\tau$;
--   3. if all A-jobs have been scheduled and no B-job can be scheduled last, the algorithm stops: the instance is not feasible.
--
--   This module defines the property "the sequence $\sigma$ can be produced by this rule": for every position $m$ of $\sigma$, with $U$ the jobs in positions $0,\dots,m$ and $\bar\tau=C_{\sigma(m)}(\sigma)$, the job $\sigma(m)$ obeys 1 when an eligible B-job exists in $U$ and obeys 2 otherwise. Ties are broken arbitrarily, so the property admits every tie-break. A position at which the rule stops (case 3) admits no job, so a complete sequence with this property exists exactly when the rule never stops.
--
--   **Formalization Note** The algorithm is encoded as a property of its finished output, in the style of the published `LawlerPrec.MinMax.IsLawlerSequence`. Positions are 0-based; $\bar\tau$ is `completionAt p l m`, the completion time of the job placed at position $m$, which equals the total processing time of the jobs in positions $0,\dots,m$. The property does not itself require the sequence to contain every job; theorems that use it add that requirement.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 232, §4, the algorithm paragraph ("In view of the above reduction, Lawler's algorithm for this special case may be sketched as follows …")

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Model

namespace TwoAgentSched.MaxMax

/-- The sequence `l` can be produced by the backward rule of §4 (p. 232), with ties broken
arbitrarily. The rule fills the positions from last to first; when the (0-based) position `m` is
filled, the unscheduled jobs are `U = {l[0], …, l[m]}`, and the job placed there ends at
`τ̄ = completionAt p l m`, the sum of the processing times of the jobs of `U`. For every
position `m`:
1. if some B-job `k ∈ U` has `f^B_k(τ̄) ≤ Q`, then `l[m]` is such a B-job (any of them);
2. if there is no such B-job, then `l[m]` is an A-job `h` with `f^A_h(τ̄) ≤ f^A_{h'}(τ̄)` for
   every A-job `h' ∈ U`.
The rule stops ("the instance is not feasible") when no B-job of `U` satisfies 1 and `U` holds
no A-job; such a position admits no choice of `l[m]`, so no sequence through it satisfies this
property. -/
def IsBackwardRuleSeq {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (l : List (Job nA nB)) : Prop :=
  ∀ (m : ℕ) (hm : m < l.length),
    ((∃ k : Fin nB, Sum.inr k ∈ (l.take (m + 1)).toFinset ∧
        fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) →
      ∃ k : Fin nB, l[m] = Sum.inr k ∧ fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) ∧
    ((¬ ∃ k : Fin nB, Sum.inr k ∈ (l.take (m + 1)).toFinset ∧
        fB k (MooreLateJobs.Shared.completionAt p l m) ≤ Q) →
      ∃ h : Fin nA, l[m] = Sum.inl h ∧
        ∀ h' : Fin nA, Sum.inl h' ∈ (l.take (m + 1)).toFinset →
          fA h (MooreLateJobs.Shared.completionAt p l m) ≤
            fA h' (MooreLateJobs.Shared.completionAt p l m))

end TwoAgentSched.MaxMax


