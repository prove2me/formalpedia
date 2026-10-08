-- Prove2me | Definitions.Def_FlowJobShop_PairGroups_FlowShop
-- name    : FlowJobShop_PairGroups_FlowShop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:17:07.097993+00:00
-- url     : https://prove2.me/theorems/6dff7c2f-234e-49c4-a761-2f957aa73b85
-- title:
--   Flow shops, feasible non-preemptive schedules, finish time and OFT schedules (p. 36)
-- statement:
--   A **flow shop** has $m$ processors $P_1,\dots,P_m$ and $n$ jobs. Every job $i$ consists of $m$ tasks; task $j$ of job $i$ must be performed on processor $P_j$ and requires processing time $t_{j,i}\ge 0$. Zero processing times are allowed.
--
--   A **non-preemptive schedule** assigns to every task a start time $s_{j,i}$; the task is then processed without interruption during $[s_{j,i},\, s_{j,i}+t_{j,i})$. The schedule is **feasible** when
--
--   1. it starts at time zero: $s_{j,i}\ge 0$ for all $j,i$;
--   2. for every job $i$, task $j+1$ begins only after task $j$ has been completed:
--   $$s_{j,i}+t_{j,i}\le s_{j+1,i}\qquad (1\le j<m);$$
--   3. on every processor, two tasks of different jobs with positive processing times are not processed at the same time: their intervals $[s_{j,i}, s_{j,i}+t_{j,i})$ and $[s_{j,i'}, s_{j,i'}+t_{j,i'})$ are disjoint. A task of time zero occupies no processor time.
--
--   The **finish time** of a schedule $s$ is the time at which all tasks of all jobs have been completed,
--   $$\mathrm{FT}(s)=\max\Big(0,\ \max_{j,i}\,(s_{j,i}+t_{j,i})\Big),$$
--   which is $0$ when there is no task. An **optimal finish time (OFT) schedule** is a feasible schedule whose finish time is at most that of every feasible schedule of the same flow shop.
--
--   These are the objects in which the approximation bound for heuristic H (Lemma 11) is stated.
--
--   **Formalization Note** Processors are `Fin m` and jobs `Fin n`, both 0-based ($P_1$ is `0`). Times are real numbers. Precedence is stated for consecutive tasks only, which implies it for all earlier tasks since times are nonnegative. The finish time is a fold of `max` with baseline `0` over all tasks, so it is defined for $m=0$ or $n=0$. A zero-time task started late counts in the finish time; this cannot lower any finish time, and an optimal schedule never delays one.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 36 (introduction: flow shops, finish time FT(S), OFT schedules)

import Mathlib

namespace FlowJobShop.PairGroups

/-- A **flow shop** (Gonzalez–Sahni 1978, p. 36) with `m` processors `P_1, …, P_m`, indexed by
`Fin m` (`P_1 = 0`), and `n` jobs, indexed by `Fin n`. Task `j` of job `i` is performed on
processor `P_j` and takes time `t j i = t_{j,i} ≥ 0`; zero task times are allowed. -/
structure FlowShop (m n : ℕ) where
  /-- the processing time `t_{j,i}` of task `j` of job `i` -/
  t : Fin m → Fin n → ℝ
  t_nonneg : ∀ j i, 0 ≤ t j i

namespace FlowShop

variable {m n : ℕ}

/-- A **non-preemptive schedule** of the flow shop `F` is given by start times: task `j` of job
`i` is processed on `P_j` without interruption during `[s j i, s j i + t_{j,i})`. It is
**feasible** when
1. it starts at time zero: every `s j i ≥ 0`;
2. for every job, task `j + 1` starts only after task `j` has completed:
   `s j i + t_{j,i} ≤ s (j+1) i`;
3. two tasks of different jobs with positive times on the same processor do not overlap
   (their half-open intervals are disjoint). A task of time zero occupies no processor time. -/
def IsFeasible (F : FlowShop m n) (s : Fin m → Fin n → ℝ) : Prop :=
  (∀ j i, 0 ≤ s j i) ∧
  (∀ (i : Fin n) (j j' : Fin m), j.val + 1 = j'.val → s j i + F.t j i ≤ s j' i) ∧
  (∀ (j : Fin m) (i i' : Fin n), i ≠ i' → 0 < F.t j i → 0 < F.t j i' →
      s j i + F.t j i ≤ s j i' ∨ s j i' + F.t j i' ≤ s j i)

/-- The **finish time** `FT(s)`: the time at which all tasks of all jobs have been completed,
i.e. the largest completion time `s j i + t_{j,i}`, with baseline `0` (the schedule starts at
time zero; `FT = 0` when there is no task). -/
noncomputable def finishTime (F : FlowShop m n) (s : Fin m → Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin m × Fin n)).fold max 0 (fun p => s p.1 p.2 + F.t p.1 p.2)

/-- An **optimal finish time (OFT) schedule**: a feasible schedule whose finish time is at most
that of every feasible schedule of the same flow shop. -/
def IsOptimal (F : FlowShop m n) (s : Fin m → Fin n → ℝ) : Prop :=
  F.IsFeasible s ∧ ∀ s' : Fin m → Fin n → ℝ, F.IsFeasible s' → F.finishTime s ≤ F.finishTime s'

end FlowShop

end FlowJobShop.PairGroups


