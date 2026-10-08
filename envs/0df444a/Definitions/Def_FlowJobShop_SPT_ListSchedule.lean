-- Prove2me | Definitions.Def_FlowJobShop_SPT_ListSchedule
-- name    : FlowJobShop_SPT_ListSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:17:04.043049+00:00
-- url     : https://prove2.me/theorems/89ea8cb6-308c-4bd4-8799-e824de0471b1
-- title:
--   SPT orders and the SPT list schedule of a job shop (pp. 46–47)
-- statement:
--   Let a job shop with $m$ processors and $n$ jobs be given, and let $L_i$ be the sum of the task times of job $i$. A bijection $\sigma$ of $\{0,\dots,n-1\}$ lists the jobs in the order $\sigma(0),\sigma(1),\dots,\sigma(n-1)$; it is an **SPT order** if
--   $$
--   L_{\sigma(0)}\le L_{\sigma(1)}\le\cdots\le L_{\sigma(n-1)},
--   $$
--   with ties broken arbitrarily.
--
--   For any list $\sigma$, the **list schedule** processes the jobs $\sigma(0),\sigma(1),\dots$ in turn and the tasks of each job in their own order. A task of the current job that runs on processor $P$ starts at
--   $$
--   \max\bigl(\text{completion of the job's previous task, or } 0;\ \text{latest completion of a task already placed on } P\text{, or } 0\bigr)
--   $$
--   and runs for its processing time. A zero-time task completes when its preceding task completes and leaves processor availability unchanged. Tasks of consecutive jobs may overlap in time on different processors. When $\sigma$ is an SPT order this is the **SPT schedule** of Gonzalez and Sahni, "processing jobs in order of nondecreasing $L_i$".
--
--   The SPT schedule is the heuristic whose mean flow time Lemma 9 compares with the optimum. It is defined by what the heuristic computes, so the comparison cannot be witnessed by an optimal schedule.
--
--   **Formalization Note** The construction is a fold over the positions $0,\dots,n-1$, carrying for each processor the latest completion time placed on it and the start times assigned so far, with an inner fold over the tasks of the current job carrying the completion time of the job's previous task. `IsSPTOrder inst σ` is `Monotone (fun k => jobLength (σ k))`; the theorems quantify over every such $\sigma$, so no tie-break is fixed.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 46–47 (definition of SPT, 'processing jobs in order of nondecreasing L_i'; the list schedule is the one computed in Example 2, p. 47)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.SPT

open JobShopLTAS.Core

variable {m n : ℕ}

/-- `σ` lists the jobs in an SPT order (Gonzalez–Sahni 1978, pp. 46–47): the job in position `k`
is `σ k`, and the total task times `L_j = jobLength j` are nondecreasing along the list. Ties may be
broken arbitrarily. -/
def IsSPTOrder (inst : Instance m n) (σ : Fin n ≃ Fin n) : Prop :=
  Monotone fun k => inst.jobLength (σ k)

/-- The state of the list-scheduling construction: for every processor, the latest completion
time of a task already placed on it (`0` if none), and the start times assigned so far. -/
structure ListState (inst : Instance m n) where
  avail : Fin m → ℝ
  start : inst.Op → ℝ

/-- Place task `i` of job `j`. The second component of the state is the completion time of the
job's previous task (`0` before its first task). A positive-time task starts at the later of
that time and the processor's availability. A zero-time task completes when the preceding task
completes and does not change processor availability. -/
noncomputable def placeTask (inst : Instance m n) (j : Fin n) (st : ListState inst × ℝ)
    (i : Fin (inst.μ j)) : ListState inst × ℝ :=
  let b := if inst.p j i = 0 then st.2 else max st.2 (st.1.avail (inst.π j i))
  let c := b + inst.p j i
  let avail := if inst.p j i = 0 then st.1.avail else
    Function.update st.1.avail (inst.π j i) c
  (⟨avail, Function.update st.1.start ⟨j, i⟩ b⟩, c)

/-- Place all tasks of job `j`, in their own order. -/
noncomputable def placeJob (inst : Instance m n) (st : ListState inst) (j : Fin n) :
    ListState inst :=
  ((List.finRange (inst.μ j)).foldl (placeTask inst j) (st, 0)).1

/-- The non-preemptive list schedule that processes the jobs `σ 0, σ 1, …` in turn, each
job's tasks in their own order, every task starting as soon as its job's previous task has
completed and every positive-time task already placed on its processor has completed. When `σ` is an SPT order
(`IsSPTOrder`) this is the SPT schedule of Gonzalez–Sahni 1978, pp. 46–47. -/
noncomputable def listSchedule (inst : Instance m n) (σ : Fin n ≃ Fin n) : inst.Op → ℝ :=
  ((List.finRange n).foldl (fun st k => placeJob inst st (σ k))
    (⟨fun _ => 0, fun _ => 0⟩ : ListState inst)).start

end FlowJobShop.SPT


