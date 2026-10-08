-- Prove2me | Definitions.Def_BurnInBatch_BatchLPT_Model
-- name    : BurnInBatch_BatchLPT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:42.783568+00:00
-- url     : https://prove2.me/theorems/e05904af-5e61-4abe-ab5e-5a6fb6400362
-- title:
--   §2 and §5: parallel batch processing machines, the optimal makespan $C^*$ and the optimal maximum lateness $L^*$
-- statement:
--   **Jobs and batches.** There are $n$ jobs $j = 0, \dots, n-1$ (the paper's job $j+1$), job $j$ with processing time $p_j$ and, where needed, due date $d_j$. All jobs are available at time $0$. Each of $m$ identical **batch processing machines** processes up to $B$ jobs simultaneously; a batch, once started, runs to completion, and the **processing time of a batch** $P$ is that of its longest job,
--   $$p(P) = \max_{j \in P} p_j .$$
--
--   A **valid batching** is a list $S = (P_0, \dots, P_{M-1})$ of nonempty, pairwise disjoint sets of jobs, each with at most $B$ jobs, whose union is the whole job set. Batch sizes and the grouping of the jobs are arbitrary.
--
--   **Parallel batch schedules.** A schedule is a valid batching $S$ together with an assignment $\sigma$ of its batches to the machines; every machine processes its batches back to back from time $0$, in the order of the list $S$. The completion time of batch $P_k$ is the total processing time of the batches $P_{k'}$ with $k' \le k$ and $\sigma(k') = \sigma(k)$, and a job completes with its batch. Every processing order on a machine is obtained by reordering $S$.
--
--   **Optimal values.** The optimal makespan of $P/B/C_{\max}$ is
--   $$C^* = \min_{S}\ \min_{\sigma}\ \max_{i} \sum_{k : \sigma(k) = i} p(P_k),$$
--   the minimum over all valid batchings $S$ and all assignments $\sigma$ of the largest machine load. The maximum lateness of a schedule is $L_{\max} = \max_j (C_j - d_j)$, and $L^*$ is its minimum over all valid batchings and assignments. Finally $d_{\max} = \max_j d_j$.
--
--   These are the objects of Propositions 2, 3 and 5 of the paper: the optimum ranges over every way of forming the batches, not only over batches of consecutive jobs.
--
--   **Formalization Note.** The machine loads and the per-batching optimum reuse the published definitions `NumStochOpt.ListScheduling.machineLoad`, `makespan` and `optMakespan`, applied to the item sequence `batchTimes p S` (item $k$ is $p(P_k)$ for $k < M$, and $0$ beyond, where it is never read). Schedules are semi-active (no inserted idle time), which loses nothing for the regular objectives $C_{\max}$ and $L_{\max}$. The minima are real infima over finitely many valid batchings (at most $n$ disjoint nonempty batches) and finitely many assignments, nonempty when $B \ge 1$ and $m \ge 1$, so they are attained; every theorem assumes $0 < B$ and $0 < m$. `batchTime` is $0$ on the empty batch, which never occurs in a valid batching; `scheduleLmax` and `dMax` are $0$ when $n = 0$, and the theorem that uses them assumes $n \ge 1$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 766, §2, Assumptions 1–3; p. 771, §5 ("m parallel identical batch processing machines and all jobs are available simultaneously"); p. 773, definition of L*, d_max

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

/-- A valid batching of the jobs `0, …, n-1` into batches of at most `B` jobs (Assumption 2,
p. 766): every batch is nonempty and holds at most `B` jobs, distinct batches are disjoint,
and every job lies in some batch. The list order is the order in which the batches are
listed; it carries no meaning for the makespan. -/
def IsBatching (n B : ℕ) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty ∧ P.card ≤ B) ∧ S.Pairwise Disjoint ∧ ∀ j : Fin n, ∃ P ∈ S, j ∈ P

/-- `C*`, the optimal makespan of `P/B/C_max` (§5, p. 771): the minimum, over all valid
batchings `S` (any batch sizes `≤ B`, any grouping of jobs) and all assignments of the
batches to the `m` identical machines, of the largest machine load, where a batch occupies
its machine for its batch time. All jobs are available at time `0`. -/
noncomputable def optBatchMakespan (n m B : ℕ) (p : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : List (Finset (Fin n)) // IsBatching n B S},
    optMakespan S.1.length m (BurnInBatch.ListSched.batchTimes p S.1)

/-- Completion time of batch `k` when the batches of `S` (with item times `q`) are assigned
to machines by `σ` and each machine processes its batches back to back from time `0` in list
order: the total time of the batches `k' ≤ k` on the machine of `k`. -/
def batchCompletion {M m : ℕ} (q : ℕ → ℝ) (σ : Fin M → Fin m) (k : Fin M) : ℝ :=
  ∑ k' : Fin M, if k' ≤ k ∧ σ k' = σ k then q (k' : ℕ) else 0

/-- Completion time of job `j` given the completion times `c` of the batches of `S`: the
completion time of the batch containing `j` (in a valid batching that batch is unique). -/
def jobCompletion {n : ℕ} (S : List (Finset (Fin n))) (c : Fin S.length → ℝ) (j : Fin n) : ℝ :=
  ∑ k : Fin S.length, if j ∈ S.get k then c k else 0

/-- The maximum lateness `L_max = max_j (C_j - d_j)` of the parallel batch schedule given
by the batching `S` and the assignment `σ` (each machine in list order, no idle time). -/
noncomputable def scheduleLmax {n m : ℕ} (p d : Fin n → ℝ) (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) : ℝ :=
  ⨆ j : Fin n, (jobCompletion S (batchCompletion (BurnInBatch.ListSched.batchTimes p S) σ) j - d j)

/-- `L*`, the optimal maximum lateness of `P/B/L_max` (p. 773): the minimum of
`scheduleLmax` over all valid batchings and all assignments. Every processing order on a
machine is represented by a reordering of `S`. -/
noncomputable def optLmax (n m B : ℕ) (p d : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : List (Finset (Fin n)) // IsBatching n B S},
    ⨅ σ : Fin S.1.length → Fin m, scheduleLmax p d S.1 σ

/-- `d_max`, the largest due date. -/
noncomputable def dMax {n : ℕ} (d : Fin n → ℝ) : ℝ := ⨆ j : Fin n, d j

end BurnInBatch.BatchLPT


