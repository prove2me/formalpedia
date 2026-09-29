-- Prove2me | Definitions.Def_AvgCompletionSched_BestAlpha_Model
-- name    : AvgCompletionSched_BestAlpha_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:46:00.0684+00:00
-- url     : https://prove2.me/theorems/29910f2b-9a35-4eb7-84cb-fe15a32a89ab
-- title:
--   One-machine scheduling with release dates: preemptive schedules, $\alpha$-points and $\alpha$-schedules
-- statement:
--   This file sets up the model of §2 of Chekuri, Motwani, Natarajan and Stein: nonpreemptive scheduling on one machine with release dates.
--
--   **Instance.** There are $n$ jobs $J_0,\dots,J_{n-1}$; job $J_j$ has processing time $p_j>0$ and release date $r_j\ge 0$. Weights $w_j>0$ are supplied separately by the statements whose objective is weighted.
--
--   **Preemptive schedule.** A preemptive one-machine schedule $P$ is a map $\sigma:\mathbb R\to\{\text{idle}\}\cup\{J_0,\dots,J_{n-1}\}$ giving the job that runs at each time. For every job $J_j$: the set of times at which $J_j$ runs is measurable, contained in $[\max(0,r_j),\infty)$ and bounded above, and has Lebesgue measure exactly $p_j$. Since $\sigma$ is a function, at most one job runs at any time. Let
--   $$\mathrm{done}_j(t)=\bigl|\{s\in[0,t): \sigma(s)=J_j\}\bigr|$$
--   be the amount of $J_j$ processed before time $t$. The **completion time** of $J_j$ is $C^P_j=\inf\{t:\mathrm{done}_j(t)\ge p_j\}$, and for $\alpha\in(0,1]$ its **$\alpha$-point** is
--   $$C^P_j(\alpha)=\inf\{t:\mathrm{done}_j(t)\ge \alpha p_j\},$$
--   the time at which an $\alpha$-fraction of $J_j$ is completed. For a job $J_i$, $T_i$ is the total idle time of $P$ in $[0,C^P_i)$, and $x_{ij}=\mathrm{done}_j(C^P_i)/p_j\in[0,1]$ is the fraction of $J_j$ completed before $C^P_i$; in the paper's notation $J_j\in S^P_i(\beta)$ exactly when $\beta=x_{ij}$.
--
--   **Nonpreemptive schedule.** A nonpreemptive one-machine schedule assigns each job a start time $S_j\ge r_j$ such that the intervals $[S_j,S_j+p_j)$ are pairwise disjoint; the completion time of $J_j$ is $C_j=S_j+p_j$.
--
--   **List scheduling and $\alpha$-schedules.** Given an ordering $\pi$ of the jobs, one-machine list scheduling runs the jobs nonpreemptively in the order $\pi$, each starting at the later of its release date and the completion time of the previous job in the list (the machine is free from time $0$). An ordering is an **$\alpha$-order** of $P$ if it lists the jobs in nondecreasing order of $C^P_j(\alpha)$; list scheduling in an $\alpha$-order is an **$\alpha$-schedule**. $C^\alpha_j$ denotes the completion time of $J_j$ in the $\alpha$-schedule whose ties between equal $\alpha$-points are broken by job index.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** Jobs are `Fin n`, times are real. The completion time and the $\alpha$-points are real infima of sets that are nonempty (each job is processed only before a finite time) and bounded below by $0$. The paper's sums over $\beta$ become sums over jobs: $\sum_{0<\beta\le1}\beta S^P_i(\beta)=\sum_j x_{ij}p_j$. List scheduling is strict: a job never overtakes an earlier job of the list, and idle time is inserted when the next job of the list is not yet released.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 146–147 §1 (model), p. 148 (α-points, α-schedules), pp. 150–151 §2 (C^P_i, C^α_i, S^P_i(β), T_i)

import Mathlib

namespace AvgCompletionSched.BestAlpha

open MeasureTheory

/-- A one-machine scheduling instance with release dates: `n` jobs `0, …, n-1`, job `j` has
processing time `p j > 0` and release date `r j ≥ 0` (Chekuri–Motwani–Natarajan–Stein 2001, §1,
pp. 146–147). Weights are passed separately where the paper's objective is weighted. -/
structure Instance (n : ℕ) where
  /-- processing times -/
  p : Fin n → ℝ
  /-- release dates -/
  r : Fin n → ℝ
  p_pos : ∀ j, 0 < p j
  r_nonneg : ∀ j, 0 ≤ r j

/-- A preemptive schedule on one machine: `σ t = some j` means job `j` runs at time `t`,
`σ t = none` means the machine is idle. A job runs only at times `t ≥ 0` and `t ≥ r j`,
receives exactly `p j` units of processing in total, and is processed only before some finite
time. -/
structure PreemptiveSchedule {n : ℕ} (I : Instance n) where
  /-- the job running at each time (`none` = idle) -/
  σ : ℝ → Option (Fin n)
  measurableSet_run : ∀ j, MeasurableSet {s | σ s = some j}
  nonneg : ∀ t j, σ t = some j → 0 ≤ t
  released : ∀ t j, σ t = some j → I.r j ≤ t
  total : ∀ j, volume {s | σ s = some j} = ENNReal.ofReal (I.p j)
  bounded : ∀ j, ∃ T : ℝ, ∀ s, σ s = some j → s < T

variable {n : ℕ} {I : Instance n}

/-- Amount of job `j` processed in `P` during `[0, t)`. -/
noncomputable def PreemptiveSchedule.done (P : PreemptiveSchedule I) (j : Fin n) (t : ℝ) : ℝ :=
  (volume ({s | P.σ s = some j} ∩ Set.Ico 0 t)).toReal

/-- Completion time `C^P_j` of job `j` in the preemptive schedule `P`: the first time at which
all `p j` units of `j` have been processed. -/
noncomputable def PreemptiveSchedule.CP (P : PreemptiveSchedule I) (j : Fin n) : ℝ :=
  sInf {t | I.p j ≤ P.done j t}

/-- The `α`-point `C^P_j(α)`: the first time at which an `α`-fraction (`α * p j` units) of job
`j` has been processed in `P` (p. 148). Used for `α ∈ (0, 1]`. -/
noncomputable def PreemptiveSchedule.CPα (P : PreemptiveSchedule I) (j : Fin n) (α : ℝ) : ℝ :=
  sInf {t | α * I.p j ≤ P.done j t}

/-- `T_i`: total idle time of `P` in `[0, C^P_i)` (p. 151). -/
noncomputable def PreemptiveSchedule.idle (P : PreemptiveSchedule I) (i : Fin n) : ℝ :=
  (volume ({s | P.σ s = none} ∩ Set.Ico 0 (P.CP i))).toReal

/-- `x_{ij}`: the fraction of job `j` completed in `P` before `C^P_i`; job `j` belongs to
`S^P_i(β)` exactly when `β = frac i j` (p. 151). -/
noncomputable def PreemptiveSchedule.frac (P : PreemptiveSchedule I) (i j : Fin n) : ℝ :=
  P.done j (P.CP i) / I.p j

/-- A nonpreemptive one-machine schedule: job `j` runs without interruption on
`[S j, S j + p j)`, not before its release date, and no two jobs overlap. -/
structure NonpreemptiveSchedule {n : ℕ} (I : Instance n) where
  /-- start times -/
  S : Fin n → ℝ
  released : ∀ j, I.r j ≤ S j
  noOverlap : ∀ i j, i ≠ j → S i + I.p i ≤ S j ∨ S j + I.p j ≤ S i

/-- Completion time `S j + p j` of job `j` in a nonpreemptive schedule. -/
def NonpreemptiveSchedule.C (N : NonpreemptiveSchedule I) (j : Fin n) : ℝ :=
  N.S j + I.p j

/-- One-machine list scheduling in the order `π` (`π k` is the `k`-th job of the list): the jobs
run nonpreemptively in list order, each starting as early as possible, i.e. at the later of its
release date and the completion of the previous job. `listFinish I π k` is the time at which the
first `k` jobs of the list are done (`0` for `k = 0`). -/
noncomputable def listFinish (I : Instance n) (π : Fin n ≃ Fin n) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
    if h : k < n then max (I.r (π ⟨k, h⟩)) (listFinish I π k) + I.p (π ⟨k, h⟩)
    else listFinish I π k

/-- Completion time of job `j` in the one-machine list schedule with order `π`. -/
noncomputable def listCompletion (I : Instance n) (π : Fin n ≃ Fin n) (j : Fin n) : ℝ :=
  listFinish I π ((π.symm j : ℕ) + 1)

/-- The order `π` lists the jobs in nondecreasing order of their `α`-points in `P`
(ties in any order). List scheduling in such an order is an `α`-schedule (p. 148). -/
def IsAlphaOrder (P : PreemptiveSchedule I) (α : ℝ) (π : Fin n ≃ Fin n) : Prop :=
  ∀ k l : Fin n, k ≤ l → P.CPα (π k) α ≤ P.CPα (π l) α

/-- The canonical `α`-order: jobs sorted by `α`-point, ties broken by job index. -/
noncomputable def alphaOrder (P : PreemptiveSchedule I) (α : ℝ) : Fin n ≃ Fin n :=
  Tuple.sort (fun j => toLex (P.CPα j α, j))

/-- `C^α_j`: completion time of job `j` in the `α`-schedule derived from `P`, with the canonical
tie-break of `alphaOrder`. -/
noncomputable def PreemptiveSchedule.Calpha (P : PreemptiveSchedule I) (α : ℝ) (j : Fin n) : ℝ :=
  listCompletion I (alphaOrder P α) j

end AvgCompletionSched.BestAlpha


