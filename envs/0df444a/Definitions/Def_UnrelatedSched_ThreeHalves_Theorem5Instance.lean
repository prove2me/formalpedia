-- Prove2me | Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance
-- name    : UnrelatedSched_ThreeHalves_Theorem5Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:19:59.201494+00:00
-- url     : https://prove2.me/theorems/c2f70da1-8e13-4d12-907c-714dbcdac613
-- title:
--   The scheduling instance of Theorem 5 built from a 3-dimensional matching instance
-- statement:
--   Let $T_1,\dots,T_m$ be an instance of 3-dimensional matching over $A = \{a_1,\dots,a_n\}$, $B = \{b_1,\dots,b_n\}$, $C = \{c_1,\dots,c_n\}$. The triples containing $a_j$ are the **triples of type $j$**, and $t_j$ is their number.
--
--   The scheduling instance of Theorem 5 has $m$ unrelated parallel machines, machine $i$ corresponding to the triple $T_i$, and the following jobs:
--   1. $2n$ **element jobs**, one for each $b_k$ and one for each $c_l$ (there are no jobs for the elements of $A$);
--   2. $t_j - 1$ **dummy jobs of type $j$**, for $j = 1,\dots,n$.
--
--   If $T_i = (a_j, b_k, c_l)$, machine $i$ processes
--   $$p_{i,\text{job}} = \begin{cases} 1 & \text{for the element jobs of } b_k \text{ and } c_l,\\ 2 & \text{for each dummy job of type } j,\\ 3 & \text{for every other job.}\end{cases}$$
--   All processing times are positive integers. A schedule assigns each job to one machine; the load of a machine is the sum of the processing times of its jobs and the makespan is the largest load (as in `MatousekLP.Scheduling.Schedule`).
--
--   This instance is the reduction behind Theorem 5 and Corollary 2: it has a schedule of makespan at most $2$ exactly when the matching instance has a matching.
--
--   **Formalization Note** The job set is the sum type $\mathrm{Fin}\,n \oplus \mathrm{Fin}\,n \oplus \Sigma_j \mathrm{Fin}(t_j - 1)$. The number of dummy jobs $t_j - 1$ uses truncated subtraction of natural numbers, so a type with $t_j = 0$ (an $a_j$ in no triple, a case the paper does not discuss) contributes no dummy job; such an instance has neither a matching nor a schedule of makespan at most 2. To use the published load and makespan, which index jobs by $\mathrm{Fin}\,N$, the jobs are enumerated by a fixed bijection with $\mathrm{Fin}(\text{numJobs})$, and `P` is the resulting $m \times \text{numJobs}$ matrix of natural numbers. Every statement quantifies over all schedules, so nothing depends on the chosen enumeration.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), pp. 7–8, Section 4, proof of Theorem 5

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching

namespace UnrelatedSched.ThreeHalves

/-- The number `t_j` of triples of type `j`, i.e. of triples `T_i` that contain `a_j`
(Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 7). -/
def typeCount {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (T i).1 = j)).card

/-- The jobs of the scheduling instance of Theorem 5 (p. 7): one element job for each `b_k`
(`Sum.inl k`), one element job for each `c_l` (`Sum.inr (Sum.inl l)`), and `t_j − 1` dummy jobs of
type `j` for each `j` (`Sum.inr (Sum.inr ⟨j, r⟩)`, `r < t_j − 1`). There are no jobs for the
elements of `A`.

Formalization Note: `t_j − 1` is natural-number subtraction, so a type `j` with `t_j = 0` has no
dummy job (the paper does not treat this case; the instance then has no schedule of makespan
at most `2`, and `T` has no matching). -/
abbrev Job {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) : Type :=
  Fin n ⊕ Fin n ⊕ (Σ j : Fin n, Fin (typeCount T j - 1))

/-- The processing time of a job on machine `i` in the instance of Theorem 5 (pp. 7–8). Machine
`i` corresponds to the triple `T_i = (a_j, b_k, c_l)`; it processes each of the element jobs of
`b_k` and `c_l` in one time unit, each dummy job of type `j` in two time units, and every other
job in three time units. -/
def procTime {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m) : Job T → ℕ
  | Sum.inl k => if (T i).2.1 = k then 1 else 3
  | Sum.inr (Sum.inl l) => if (T i).2.2 = l then 1 else 3
  | Sum.inr (Sum.inr ⟨j, _⟩) => if (T i).1 = j then 2 else 3

/-- The number of jobs of the instance of Theorem 5: `2n + Σ_j (t_j − 1)`. -/
def numJobs {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) : ℕ :=
  Fintype.card (Job T)

/-- A fixed enumeration of the jobs by `Fin (numJobs T)`, so that schedules are maps
`Fin (numJobs T) → Fin m` as in `MatousekLP.Scheduling`. Every statement about this instance
quantifies over all schedules, so it does not depend on which enumeration is chosen. -/
noncomputable def jobEnum {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    Job T ≃ Fin (numJobs T) :=
  Fintype.equivFin (Job T)

/-- The processing-time matrix `p_ij` of the instance of Theorem 5, with machines `Fin m` and the
jobs enumerated by `jobEnum T`. All entries are positive integers, in `{1, 2, 3}`. -/
noncomputable def P {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    Matrix (Fin m) (Fin (numJobs T)) ℕ :=
  fun i r => procTime T i ((jobEnum T).symm r)

end UnrelatedSched.ThreeHalves


