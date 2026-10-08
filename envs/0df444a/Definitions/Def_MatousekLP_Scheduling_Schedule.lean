-- Prove2me | Definitions.Def_MatousekLP_Scheduling_Schedule
-- name    : MatousekLP_Scheduling_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:27:50.496988+00:00
-- url     : https://prove2.me/theorems/6160be1e-2f85-4a2d-9a26-8cea730522ca
-- title:
--   Schedules on unrelated machines, machine loads, makespan and optimal schedules
-- statement:
--   Consider $m$ machines $M$ and $n$ jobs $J$, and let $d_{ij}$ be the running time of job $j$ on machine $i$. A **schedule** assigns every job to exactly one machine; it is a map $\sigma : J \to M$. The **load** of machine $i$ under $\sigma$ is the total running time of the jobs assigned to it,
--   $$
--   L_i(\sigma) = \sum_{j \in J:\ \sigma(j) = i} d_{ij},
--   $$
--   and the **makespan** of $\sigma$ is the largest load, $\max_{i \in M} L_i(\sigma)$ — the time needed to finish all jobs. A schedule is **optimal** if its makespan is at most the makespan of every schedule; the makespan of an optimal schedule is the optimum makespan $t_{\mathrm{opt}}$.
--
--   These are the objects of the scheduling problem of Section 8.3 (unrelated parallel machines, minimum makespan), whose approximation by linear programming is the subject of the mission.
--
--   **Formalization Note** Machines are `Fin m` and jobs are `Fin n` (index base 0; the book's machines $1,\dots,m$ and jobs $m+1,\dots,m+n$ are two disjoint index sets). The running times form a real matrix `d : Matrix (Fin m) (Fin n) ℝ`. The makespan is the supremum `⨆ i, load d σ i` over the finite type `Fin m`, which is the maximum for $m \ge 1$ (and $0$ when $m = 0$). Since the set of schedules `Fin n → Fin m` is finite, $t_{\mathrm{opt}}$ is not written as an infimum: statements take an optimal schedule $\sigma_{\mathrm{opt}}$ as a hypothesis and use its makespan.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, pp. 149–150, §8.3 (Machine Scheduling: schedule, makespan, t_opt)

import Mathlib

namespace MatousekLP.Scheduling

/-- The total running time of the jobs that the schedule `σ` assigns to machine `i`
(Matoušek–Gärtner §8.3, p. 149): `∑_{j : σ(j) = i} d_ij`. Machines are `Fin m`, jobs are
`Fin n`, and `d i j` is the running time of job `j` on machine `i`. -/
def load {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), d i j

/-- The makespan of the schedule `σ` (p. 149): the maximum over the machines of their load.
The index type `Fin m` is finite, so the supremum is a maximum whenever `m ≥ 1`. -/
noncomputable def makespan {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) : ℝ :=
  ⨆ i : Fin m, load d σ i

/-- `σ` is an optimal schedule (p. 149): its makespan is at most the makespan of every
schedule `τ : Fin n → Fin m`. The book's `t_opt` is `makespan d σ` for such a `σ`. -/
def IsOptimalSchedule {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) : Prop :=
  ∀ τ : Fin n → Fin m, makespan d σ ≤ makespan d τ

end MatousekLP.Scheduling


