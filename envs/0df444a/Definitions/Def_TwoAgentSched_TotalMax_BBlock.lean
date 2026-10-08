-- Prove2me | Definitions.Def_TwoAgentSched_TotalMax_BBlock
-- name    : TwoAgentSched_TotalMax_BBlock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:34.28559+00:00
-- url     : https://prove2.me/theorems/b3636a9a-6ec4-4e50-ab95-c7c1307543dc
-- title:
--   §5.2.1: B-blocks of a sequence and the time intervals they occupy
-- statement:
--   B-blocks, as defined on p. 234 of Agnetis et al. (2004): "Given a feasible sequence $\sigma$, in what follows we define B-block as a maximal set of consecutive $B$-jobs in $\sigma$."
--
--   Two $B$-jobs $J^B_k$ and $J^B_{k'}$ lie in the same B-block of the sequence $\sigma$ when no $A$-job occupies a position strictly between their positions. The **B-block of $J^B_k$** is the set of all $B$-jobs in the same B-block as $J^B_k$; it always contains $J^B_k$, and the B-blocks of the $B$-jobs form the partition of the $B$-jobs into B-blocks. The **time interval** of this B-block is $[S,E]$, where
--   $$S=\min_{k'\in\text{block}}\bigl(C^B_{k'}(\sigma)-p^B_{k'}\bigr),\qquad E=\max_{k'\in\text{block}} C^B_{k'}(\sigma),$$
--   the start of its first job and the completion of its last job.
--
--   These notions state Lemma 5.6, which says that all optimal schedules share their B-blocks and the intervals they occupy.
--
--   **Formalization Note** Positions are `List.idxOf` in the sequence; the definition is meant for sequences that list every job once. The definition file also proves that every $B$-job lies in its own B-block, which is what makes the minimum and the maximum above well defined.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, definition of B-block before Lemma 5.6

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Model

namespace TwoAgentSched.TotalMax

/-- Two B-jobs `k`, `k'` lie in the same B-block of the sequence `l` (§5.2.1, p. 234: "a maximal
set of consecutive B-jobs in σ"): no A-job occupies a position strictly between the positions
of `J^B_k` and `J^B_{k'}` in `l`. Positions are `List.idxOf`; `l` is meant to be a schedule of
all jobs. -/
def SameBBlock {nA nB : ℕ} (l : List (TwoAgentSched.MaxMax.Job nA nB)) (k k' : Fin nB) : Prop :=
  ∀ h : Fin nA,
    ¬ (min (l.idxOf (Sum.inr k : TwoAgentSched.MaxMax.Job nA nB)) (l.idxOf (Sum.inr k' : TwoAgentSched.MaxMax.Job nA nB)) <
          l.idxOf (Sum.inl h : TwoAgentSched.MaxMax.Job nA nB) ∧
        l.idxOf (Sum.inl h : TwoAgentSched.MaxMax.Job nA nB) <
          max (l.idxOf (Sum.inr k : TwoAgentSched.MaxMax.Job nA nB)) (l.idxOf (Sum.inr k' : TwoAgentSched.MaxMax.Job nA nB)))

open Classical in
/-- The B-block of the B-job `J^B_k` in the sequence `l` (§5.2.1, p. 234): the set of B-jobs
in the maximal run of consecutive B-jobs of `l` that contains `J^B_k`. -/
noncomputable def bBlock {nA nB : ℕ} (l : List (TwoAgentSched.MaxMax.Job nA nB)) (k : Fin nB) : Finset (Fin nB) :=
  Finset.univ.filter (fun k' => SameBBlock l k k')

/-- Every B-job lies in its own B-block. -/
theorem mem_bBlock_self {nA nB : ℕ} (l : List (TwoAgentSched.MaxMax.Job nA nB)) (k : Fin nB) : k ∈ bBlock l k := by
  classical
  rw [bBlock, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro h hh
  rw [min_self, max_self] at hh
  exact lt_irrefl _ (lt_trans hh.1 hh.2)

/-- The start of the time interval occupied by the B-block of `J^B_k` in `l`: the earliest
starting time `C^B_{k'} − p^B_{k'}` of a B-job `k'` of the block. -/
noncomputable def blockStart {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (l : List (TwoAgentSched.MaxMax.Job nA nB))
    (k : Fin nB) : ℝ :=
  (bBlock l k).inf' ⟨k, mem_bBlock_self l k⟩
    (fun k' => MooreLateJobs.Shared.completionTime p l (Sum.inr k') - p (Sum.inr k'))

/-- The end of the time interval occupied by the B-block of `J^B_k` in `l`: the latest
completion time `C^B_{k'}` of a B-job `k'` of the block. -/
noncomputable def blockEnd {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (l : List (TwoAgentSched.MaxMax.Job nA nB))
    (k : Fin nB) : ℝ :=
  (bBlock l k).sup' ⟨k, mem_bBlock_self l k⟩
    (fun k' => MooreLateJobs.Shared.completionTime p l (Sum.inr k'))

end TwoAgentSched.TotalMax


