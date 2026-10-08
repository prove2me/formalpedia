-- Prove2me | Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
-- name    : FlowJobShop_PartitionFlow_FlowShop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:05.908983+00:00
-- url     : https://prove2.me/theorems/c72f5c93-2298-4bf4-ad4a-7dcb213018de
-- title:
--   Flow shops, preemptive and non-preemptive schedules, job finish times $f_i(S)$ and finish time $\mathrm{FT}(S)$ (p. 36; footnote 1, p. 40)
-- statement:
--   A **flow shop** with $m\ge 1$ processors $P_1,\dots,P_m$ and a finite set of jobs $J$ is given by task times $t_{j,i}\ge 0$, $1\le j\le m$, $i\in J$: task $j$ of job $i$ must be performed on processor $P_j$ and needs $t_{j,i}$ units of processing. Task times may be zero.
--
--   A **preemptive schedule** $S$ is described, as in the paper, by pieces: a piece $(s,f)$ of task $j$ of job $i$ means that this task is processed on $P_j$ during the half-open interval $[s,f)$. The schedule assigns to every task a finite set of pieces such that
--
--   1. every piece satisfies $0\le s<f$ (the schedule starts at time zero);
--   2. two different pieces on the same processor do not overlap: their half-open intervals are disjoint;
--   3. the lengths $f-s$ of the pieces of task $j$ of job $i$ add up to $t_{j,i}$ (so a task of time zero has no piece);
--   4. for each job $i$ and tasks $j<j'$, every piece of task $j'$ starts no earlier than the end of every piece of task $j$: task $j'$ of a job is processed only after the earlier tasks of that job have been completed.
--
--   A schedule is **non-preemptive** if every task is processed in at most one piece (one piece of length $t_{j,i}$ when $t_{j,i}>0$, none when $t_{j,i}=0$).
--
--   For a schedule $S$, $f_i(S)$ is the time at which all tasks of job $i$ have been completed: the latest end of a piece of a task of job $i$, and $0$ when all tasks of job $i$ have time zero. The **finish time** is
--   $$\mathrm{FT}(S)=\max_{i\in J} f_i(S),$$
--   taken to be $0$ when there are no jobs. Finally, the flow shop has **at most two nonzero tasks per job** if for every job $i$ at most two of $t_{1,i},\dots,t_{m,i}$ are nonzero.
--
--   These are the objects in which the paper's NP-completeness results for flow shops are stated: "FOFT" asks whether a schedule with $\mathrm{FT}(S)\le\tau$ exists.
--
--   **Formalization Note** Processors are `Fin m`, with $P_1$ the index `0`. A schedule stores, for each task, a `Finset` of pairs `(s, f)` of reals; a non-preemptive schedule is the special case of at most one piece per task, so a single structure carries both kinds and a single finish-time definition. Condition 4 is imposed for all earlier tasks rather than only the immediately preceding one; this is equivalent to the paper's rule (task $j$ starts after task $j-1$ is completed) and makes a zero task, which has no piece, transmit the completion of the tasks before it. $f_i(S)$ and $\mathrm{FT}(S)$ are maxima with baseline $0$ (`Finset.fold max 0`).
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 36 (model, f_i(S), FT(S)); p. 38 ("at most two nonzero tasks"); p. 40, footnote 1 (pieces of a preemptive schedule)

import Mathlib

namespace FlowJobShop.PartitionFlow

/-- A flow shop (Gonzalez–Sahni 1978, p. 36): `m` processors `P_1, …, P_m`, indexed by `Fin m`
(`P_1 = 0`), and a set of jobs indexed by a type `J`. Task `j` of job `i` must be performed on
processor `P_j` and takes time `t j i = t_{j,i} ≥ 0`. Zero task times are allowed. -/
structure FlowShop (m : ℕ) (J : Type*) where
  /-- processing time `t_{j,i}` of task `j` of job `i` -/
  t : Fin m → J → ℝ
  t_nonneg : ∀ j i, 0 ≤ t j i
  /-- the paper assumes at least one processor -/
  m_pos : 0 < m

namespace FlowShop

variable {m : ℕ} {J : Type*}

/-- A **preemptive schedule** of a flow shop, in the paper's own representation (footnote 1,
p. 40): the work of processor `P_j` is a finite collection of pieces, a piece `(s, f)` of task
`j` of job `i` meaning that this task is processed on `P_j` during `[s, f)`.
`pieces j i` is the finite set of pieces of task `j` of job `i`; every piece of that task is
therefore on the task's own processor `P_j`. The conditions are:
* every piece satisfies `0 ≤ s < f` (the schedule starts at time zero);
* two different pieces on the same processor are disjoint as half-open intervals;
* the pieces of a task have total length equal to the task time (so a zero task has no piece);
* for every job, every piece of task `j'` starts no earlier than the end of every piece of
  every earlier task `j < j'` of the same job (task `j' ≥ 2` begins only after task `j' − 1`
  has completed; a zero task, having no piece, imposes the completion of the preceding tasks). -/
structure PreemptiveSchedule (F : FlowShop m J) where
  /-- the pieces `(s, f)` of task `j` of job `i` -/
  pieces : Fin m → J → Finset (ℝ × ℝ)
  start_nonneg : ∀ j i, ∀ p ∈ pieces j i, 0 ≤ p.1
  start_lt_end : ∀ j i, ∀ p ∈ pieces j i, p.1 < p.2
  disjoint : ∀ (j : Fin m) (i i' : J) (p p' : ℝ × ℝ), p ∈ pieces j i → p' ∈ pieces j i' →
    (i, p) ≠ (i', p') → p.2 ≤ p'.1 ∨ p'.2 ≤ p.1
  total_length : ∀ j i, ∑ p ∈ pieces j i, (p.2 - p.1) = F.t j i
  precedence : ∀ (i : J) (j j' : Fin m), j < j' →
    ∀ p ∈ pieces j i, ∀ p' ∈ pieces j' i, p.2 ≤ p'.1

namespace PreemptiveSchedule

variable {F : FlowShop m J}

/-- A **non-preemptive schedule** is a preemptive schedule in which every task is processed
in at most one piece (exactly one if its time is positive, none if it is zero). -/
def IsNonPreemptive (S : PreemptiveSchedule F) : Prop :=
  ∀ j i, (S.pieces j i).card ≤ 1

/-- `f_i(S)`, the time at which all tasks of job `i` have been completed: the latest end of a
piece of any task of job `i`, and `0` if every task of job `i` has time zero (the schedule
starts at time zero). -/
noncomputable def jobFinish (S : PreemptiveSchedule F) (i : J) : ℝ :=
  ((Finset.univ : Finset (Fin m)).biUnion (fun j => S.pieces j i)).fold max 0 Prod.snd

/-- The finish time `FT(S) = max_i f_i(S)` (with baseline `0`, the start of the schedule). -/
noncomputable def finishTime [Fintype J] (S : PreemptiveSchedule F) : ℝ :=
  (Finset.univ : Finset J).fold max 0 S.jobFinish

end PreemptiveSchedule

/-- The flow shop has **at most two nonzero tasks per job**: for every job `i`, at most two of
`t_{1,i}, …, t_{m,i}` are nonzero. -/
def AtMostTwoNonzeroTasks (F : FlowShop m J) : Prop :=
  ∀ i, ((Finset.univ : Finset (Fin m)).filter (fun j => F.t j i ≠ 0)).card ≤ 2

end FlowShop

end FlowJobShop.PartitionFlow


