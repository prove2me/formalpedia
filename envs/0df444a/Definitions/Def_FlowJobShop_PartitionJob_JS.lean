-- Prove2me | Definitions.Def_FlowJobShop_PartitionJob_JS
-- name    : FlowJobShop_PartitionJob_JS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:39.241241+00:00
-- url     : https://prove2.me/theorems/9641df1e-6714-4cb3-a640-b7f464e55fed
-- title:
--   The two-processor job shop JS built from a PARTITION instance (proof of Lemma 5, p. 43)
-- statement:
--   Let $a_1, \dots, a_n$ be nonnegative integers and $T = \sum_{i=1}^n a_i$. The job shop $\mathrm{JS}$ has $m = 2$ processors $P_1, P_2$ and $n+2$ jobs. Writing each task as (processor, time):
--
--   1. job $i$, $1 \le i \le n$: task 1 is $(P_2, a_i)$ and task 2 is $(P_1, a_i)$, that is $t_{2,i,1} = t_{1,i,2} = a_i$;
--   2. job $n+1$: tasks $(P_1, T/2)$, $(P_2, T/2)$, $(P_1, 3T)$, that is $t_{1,n+1,1} = t_{2,n+1,2} = T/2$ and $t_{1,n+1,3} = 3T$;
--   3. job $n+2$: tasks $(P_2, 3T)$, $(P_1, T/2)$, $(P_2, T/2)$, that is $t_{2,n+2,1} = 3T$ and $t_{1,n+2,2} = t_{2,n+2,3} = T/2$.
--
--   Each processor carries a total load of
--
--   $$
--   T + \tfrac{T}{2} + 3T + \tfrac{T}{2} \;=\; 5T .
--   $$
--
--   This is the instance of the reduction from PARTITION to preemptive and non-preemptive JOFT with target finish time $\tau = 5T$.
--
--   **Formalization Note** $\mathrm{JS}(a)$ is an `Instance 2 (n + 2)`. Processor $P_1$ is `0` and $P_2$ is `1`; jobs and tasks are 0-based, so the paper's job $i \le n$ is job $i-1$, job $n+1$ is job $n$ and job $n+2$ is job $n+1$. $T$ is `T a`, the sum cast to the reals.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 43, proof of Lemma 5 (construction of JS)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Processor of (0-based) task `k` of job `j` in `JS(a)`. Processor `P_1` is `0`, `P_2` is `1`.
Jobs `j < n` (the paper's jobs `1, …, n`) run on `P_2` then `P_1`; job `n` (the paper's job `n+1`)
on `P_1, P_2, P_1`; job `n+1` (the paper's job `n+2`) on `P_2, P_1, P_2`. -/
def jsMach {n : ℕ} (j : Fin (n + 2)) (k : ℕ) : Fin 2 :=
  if j.val < n then (if k = 0 then 1 else 0)
  else if j.val = n then (if k = 1 then 1 else 0)
  else (if k = 1 then 0 else 1)

/-- Processing time of (0-based) task `k` of job `j` in `JS(a)`:
`t_{2,i,1} = t_{1,i,2} = a_i` for the paper's jobs `i ≤ n`;
`t_{1,n+1,1} = t_{2,n+1,2} = FlowJobShop.PartitionFlow.T/2`, `t_{1,n+1,3} = 3T`;
`t_{2,n+2,1} = 3T`, `t_{1,n+2,2} = t_{2,n+2,3} = FlowJobShop.PartitionFlow.T/2`. -/
noncomputable def jsTime {n : ℕ} (a : Fin n → ℕ) (j : Fin (n + 2)) (k : ℕ) : ℝ :=
  if h : j.val < n then (a ⟨j.val, h⟩ : ℝ)
  else if j.val = n then (if k = 2 then 3 * FlowJobShop.PartitionFlow.T a else FlowJobShop.PartitionFlow.T a / 2)
  else (if k = 0 then 3 * FlowJobShop.PartitionFlow.T a else FlowJobShop.PartitionFlow.T a / 2)

lemma jsTime_nonneg {n : ℕ} (a : Fin n → ℕ) (j : Fin (n + 2)) (k : ℕ) : 0 ≤ jsTime a j k := by
  have hT : 0 ≤ FlowJobShop.PartitionFlow.T a := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (a i))
  unfold jsTime
  split_ifs <;> positivity

/-- The job shop `JS` built from a PARTITION instance `a` in the proof of Lemma 5
(Gonzalez–Sahni 1978, p. 43): `n + 2` jobs on `m = 2` processors. Jobs `j < n` have two tasks,
jobs `n` and `n + 1` (the paper's `n+1`, `n+2`) have three. -/
noncomputable def JS {n : ℕ} (a : Fin n → ℕ) : Instance 2 (n + 2) where
  μ j := if j.val < n then 2 else 3
  π j k := jsMach j k.val
  p j k := jsTime a j k.val
  p_nonneg j k := jsTime_nonneg a j k.val

end FlowJobShop.PartitionJob


