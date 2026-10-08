-- Prove2me | Definitions.Def_FlowJobShop_SPT_MeanFlowTime
-- name    : FlowJobShop_SPT_MeanFlowTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:16:49.603987+00:00
-- url     : https://prove2.me/theorems/e5f2b65b-7add-464c-bd1c-55724cac228a
-- title:
--   Finish time $f_i(S)$ and mean flow time $\mathrm{MFT}(S)$ of a job-shop schedule; the flow shop as a job shop (p. 36)
-- statement:
--   Consider a job shop with $m$ processors $P_1,\dots,P_m$ and $n$ jobs. Job $i$ is a finite sequence of tasks; task $j$ of job $i$ is processed on a prescribed processor for a time $p_{i,j}\ge 0$. A (non-preemptive) schedule $s$ assigns to every task a start time $s_{i,j}$, so that the task occupies its processor during $[s_{i,j}, s_{i,j}+p_{i,j})$.
--
--   The **finish time** of job $i$ in $s$ is the time at which all tasks of job $i$ have been completed:
--   $$
--   f_i(s)=\max\Bigl(0,\ \max_{j}\bigl(s_{i,j}+p_{i,j}\bigr)\Bigr),
--   $$
--   where the baseline $0$ reflects that every schedule starts at time zero, so that a job without tasks finishes at time $0$. The **mean flow time** of $s$ is
--   $$
--   \mathrm{MFT}(s)=\frac1n\sum_{i=1}^n f_i(s).
--   $$
--   An optimal mean flow time (OMFT) schedule is a feasible schedule of least mean flow time.
--
--   A **flow shop** is the special case in which every job $i$ has exactly $m$ tasks and task $k$ runs on processor $P_k$ for a time $t_{k,i}\ge 0$. This module records that embedding, so that every statement about job shops applies to flow shops.
--
--   These are the objective and the model of Lemma 9 of Gonzalez and Sahni.
--
--   **Formalization Note** The job-shop instance and its task times come from the published definition `JobShopLTAS.Core.Instance` (jobs `Fin n`, processors `Fin m`, 0-based task indices, real times). Feasibility is stated locally: zero-time tasks occupy no processor interval. For a feasible schedule the maximum over the tasks equals the completion time of the job's last task. For $n=0$ Lean's division returns $0$, the value of the empty average.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 36 (definitions of f_i(S), MFT(S), OMFT; the flow-shop and job-shop model)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.SPT

open JobShopLTAS.Core

variable {m n : ℕ}

/-- Feasibility in the job-shop model of Gonzalez–Sahni (p. 36). A zero-time task has an
instantaneous completion and occupies no processor interval; only positive-time tasks can
overlap on a processor. -/
structure IsPaperFeasibleSchedule (inst : Instance m n) (s : inst.Op → ℝ) : Prop where
  start_nonneg : ∀ o : inst.Op, 0 ≤ s o
  precedence : ∀ j : Fin n, ∀ i i' : Fin (inst.μ j), i.val + 1 = i'.val →
    s ⟨j, i⟩ + inst.p j i ≤ s ⟨j, i'⟩
  machine_disjoint : ∀ o o' : inst.Op, o ≠ o' → inst.mach o = inst.mach o' →
    0 < inst.proc o → 0 < inst.proc o' →
      s o + inst.proc o ≤ s o' ∨ s o' + inst.proc o' ≤ s o

/-- The finish time `f_j(s)` of job `j` in the schedule `s` (Gonzalez–Sahni 1978, p. 36): the time
at which all tasks of job `j` have been completed, i.e. the largest completion time
`s ⟨j, i⟩ + p j i` over the tasks `i` of job `j`. The schedule starts at time zero, so the
maximum is taken with baseline `0`; a job without tasks has finish time `0`. -/
noncomputable def finishTime (inst : Instance m n) (s : inst.Op → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.fold max 0 (fun i : Fin (inst.μ j) => s ⟨j, i⟩ + inst.p j i)

/-- The mean flow time `MFT(s) = (∑_j f_j(s)) / n` of the schedule `s` (p. 36). For `n = 0` Lean's
division gives `0`, which is the empty average. -/
noncomputable def meanFlowTime (inst : Instance m n) (s : inst.Op → ℝ) : ℝ :=
  (∑ j, finishTime inst s j) / n

/-- The flow shop with task times `t k i ≥ 0` (task `k` of job `i` runs on processor `P_k` for
`t k i`, p. 36), viewed as a job shop: every job has `m` tasks, and task `k` is on processor `k`. -/
def flowShop (t : Fin m → Fin n → ℝ) (ht : ∀ k i, 0 ≤ t k i) : Instance m n where
  μ := fun _ => m
  π := fun _ k => k
  p := fun i k => t k i
  p_nonneg := fun i k => ht k i

end FlowJobShop.SPT


