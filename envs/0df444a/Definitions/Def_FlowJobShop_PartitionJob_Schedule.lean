-- Prove2me | Definitions.Def_FlowJobShop_PartitionJob_Schedule
-- name    : FlowJobShop_PartitionJob_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:34.746523+00:00
-- url     : https://prove2.me/theorems/801892f8-e46a-4396-8f98-c9f8113f55df
-- title:
--   Preemptive and non-preemptive job-shop schedules, job completion times and finish time (p. 36; footnote 1, p. 40)
-- statement:
--   Fix a job shop with processors $P_1, \dots, P_m$ and jobs $1, \dots, n$, where job $i$ is a finite sequence of tasks and task $j$ of job $i$ must be performed on a given processor $k$ for a processing time $t_{k,i,j} \ge 0$. For every job, task $j \ge 2$ can begin only after task $j-1$ has been completed, and every schedule starts at time zero.
--
--   A **schedule** is a finite collection of pieces $(l, s, f)$, each meaning that task $l$ is processed on its own processor from time $s$ to time $f$ (the triple notation of the paper's footnote 1, p. 40). For a schedule $S$ and a job $i$, let $C_{i,0}(S) = 0$ and let $C_{i,j}(S)$, the **completion time of task $j$**, be the larger of $C_{i,j-1}(S)$ and the end points $f$ of the pieces of task $j$; a task of length zero has no pieces and is completed as soon as its predecessor is. The time $f_i(S)$ at which all tasks of job $i$ are completed is the completion time of its last task.
--
--   $S$ is a **preemptive schedule** if
--
--   1. every piece has positive length, $s < f$;
--   2. every piece of task $j$ of job $i$ starts no earlier than $C_{i,j-1}(S)$ (in particular at a time $\ge 0$);
--   3. two distinct pieces on the same processor do not overlap as half-open intervals $[s, f)$;
--   4. the pieces of each task have total length equal to its processing time.
--
--   $S$ is a **non-preemptive schedule** if, in addition, each task is processed in at most one piece. The schedule has **finish time at most $\tau$** if
--
--   $$
--   \mathrm{FT}(S) \;=\; \max_i f_i(S) \;\le\; \tau .
--   $$
--
--   These are the paper's objects of the problems preemptive and non-preemptive JOFT ("does the job shop have a schedule with finish time $\le \tau$?").
--
--   **Formalization Note** The job-shop data are the published `JobShopLTAS.Core.Instance` (operations `⟨j, i⟩` with 0-based task indices, machine `π j i`, time `p j i ≥ 0`). `S.completed j k` is the completion time of the first $k$ tasks of job $j$, defined by recursion on $k$ with a maximum over a finite set (baseline the previous completion), so it is always attained. A non-preemptive schedule is a preemptive one with at most one piece per task, so both notions share one finish-time definition.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 36 (model), p. 38 (JOFT), footnote 1 p. 40 (piece notation)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- A (candidate) schedule of a job shop `inst` (Gonzalez–Sahni 1978, p. 36; representation of
footnote 1, p. 40): a finite set of *pieces* `(o, s, f)`, each meaning that operation (task) `o`
is processed on its own processor `inst.mach o` during the time interval `[s, f)`. Whether the
pieces form a feasible preemptive or non-preemptive schedule is the predicate
`Schedule.IsPreemptive` / `Schedule.IsNonPreemptive` below. -/
structure Schedule {m n : ℕ} (inst : Instance m n) where
  /-- the pieces `(o, s, f)`: operation `o` is processed on `inst.mach o` from `s` to `f` -/
  pieces : Finset (inst.Op × ℝ × ℝ)

namespace Schedule

variable {m n : ℕ} {inst : Instance m n} (S : Schedule inst)

/-- `S.completed j k` is the time at which the first `k` tasks of job `j` (0-based tasks
`0, …, k-1`) have been completed: `completed j 0 = 0` (every schedule starts at time zero), and
`completed j (k+1)` is the maximum of `completed j k` and the end points `f` of all pieces of task
`k` of job `j`. A task with no pieces (a task of length zero) thus completes when the previous task
of its job completes. -/
noncomputable def completed (j : Fin n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (S.pieces.filter (fun q => q.1.1 = j ∧ q.1.2.val = k)).fold max (completed j k)
      (fun q => q.2.2)

/-- `f_j(S)`: the time at which all tasks of job `j` have been completed in `S`. -/
noncomputable def jobFinish (j : Fin n) : ℝ := S.completed j (inst.μ j)

/-- `S` is a feasible **preemptive** schedule of the job shop:
1. every piece has positive length, `s < f`;
2. task order: every piece of task `k` of job `j` starts no earlier than the completion of tasks
   `0, …, k-1` of job `j` (for `k = 0` this says the piece starts at time `≥ 0`);
3. two distinct pieces on the same processor do not overlap (as half-open intervals);
4. the pieces of each task have total length equal to the task's processing time. -/
structure IsPreemptive : Prop where
  pos_length : ∀ q ∈ S.pieces, q.2.1 < q.2.2
  task_order : ∀ q ∈ S.pieces, S.completed q.1.1 q.1.2.val ≤ q.2.1
  machine_disjoint : ∀ q ∈ S.pieces, ∀ q' ∈ S.pieces, q ≠ q' →
    inst.mach q.1 = inst.mach q'.1 → q.2.2 ≤ q'.2.1 ∨ q'.2.2 ≤ q.2.1
  total_length : ∀ o : inst.Op,
    ∑ q ∈ S.pieces.filter (fun q => q.1 = o), (q.2.2 - q.2.1) = inst.proc o

/-- `S` is a feasible **non-preemptive** schedule: a feasible preemptive schedule in which every
task is processed in at most one piece (exactly one if its time is positive, none if it is zero). -/
def IsNonPreemptive : Prop :=
  S.IsPreemptive ∧ ∀ q ∈ S.pieces, ∀ q' ∈ S.pieces, q.1 = q'.1 → q = q'

/-- `S` has finish time at most `τ`: `FT(S) = max_j f_j(S) ≤ τ`. -/
def FinishedBy (τ : ℝ) : Prop := ∀ j : Fin n, S.jobFinish j ≤ τ

end Schedule

end FlowJobShop.PartitionJob


