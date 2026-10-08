-- Prove2me | Definitions.Def_SchedComplexity_OneMachine_Model
-- name    : SchedComplexity_OneMachine_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:55.459339+00:00
-- url     : https://prove2.me/theorems/e1298610-4b1f-4df0-8be4-640e236fcfc0
-- title:
--   Single-machine instances, feasible schedules with release dates, and the criteria $L_j$, $U_j$, $\sum w_jC_j$, $\sum w_jU_j$
-- statement:
--   The single-machine scheduling model of Section 3 of Brucker, Lenstra and Rinnooy Kan.
--
--   An **instance** has $n$ jobs $J_1,\dots,J_n$; each job $J_j$ consists of a single operation on the machine $M_1$ and carries a processing time $p_{j1}$, a weight $w_j$, a release date $r_j$ and a due date $d_j$, all nonnegative integers.
--
--   A **feasible schedule** assigns to each job a starting time $B_j\in\mathbb N$ such that
--
--   1. $B_j\ge r_j$ for every job, and
--   2. the occupied intervals $[B_j,B_j+p_{j1})$ of any two distinct jobs are disjoint.
--
--   Idle time is allowed. For a schedule the paper defines the completion time $C_j=B_j+p_{j1}$, the lateness $L_j=C_j-d_j$ (an integer, possibly negative), and
--
--   $$U_j=\begin{cases}0 & C_j\le d_j,\\ 1 & \text{otherwise.}\end{cases}$$
--
--   The criteria used here are $\sum w_jC_j=\sum_{j=1}^n w_jC_j$ and $\sum w_jU_j=\sum_{j=1}^n w_jU_j$. The file also names three problem-class conditions of the paper: all jobs available at time $0$ (the default, $r_j=0$ for all $j$); the element $r_n\ge0$ (only the last job $J_n$ may have a nonzero release date; there is at least one job); and $w_j=1$. Finally it fixes how an instance with a threshold $y$ is written as a list of numbers: $n$, then $p_{j1},w_j,r_j,d_j$ for $j=1,\dots,n$ in turn, then $y$.
--
--   This model underlies the four target problems of the mission.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based, so $J_n$ is index $n-1$. Starting times are natural numbers: Section 3 computes $B_j$ from a processing order on each machine, and on nonnegative integer data such times are integers; since all criteria are regular and release dates survive left shifts, real starting times would give the same yes-instances. Condition 2 expresses that a machine handles at most one job at a time. A job with $p_{j1}=0$ occupies the empty interval. The published `DelayedSWPT.Model.IsFeasible` instead orders every pair of jobs and would exclude some such schedules.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 6-7, Section 3

import Mathlib

namespace SchedComplexity.OneMachine

/-- A single-machine instance in the sense of Section 3 (Brucker, Lenstra & Rinnooy Kan, Report
BW 43/75, p. 6): `n` jobs `J_1, …, J_n`, here `Fin n` (0-based, so `J_j` is index `j - 1` and the
last job `J_n` is index `n - 1`), each with one operation on the machine `M_1`, a processing time
`p j`, a weight `w j`, a release date `r j` and a due date `d j`, all nonnegative integers. -/
structure Instance where
  /-- The number of jobs. -/
  n : ℕ
  /-- Processing times `p_{j1}`. -/
  p : Fin n → ℕ
  /-- Weights `w_j`. -/
  w : Fin n → ℕ
  /-- Release dates `r_j`. -/
  r : Fin n → ℕ
  /-- Due dates `d_j`. -/
  d : Fin n → ℕ

namespace Instance

variable (I : Instance)

/-- A feasible schedule on the single machine, given by starting times `B j ∈ ℕ`: each job
starts no earlier than its release date, and the occupied half-open intervals
`[B j, B j + p j)` of distinct jobs are disjoint (Section 3, p. 6). Idle time is allowed.
In particular, a zero-processing-time job occupies the empty interval, as the paper's
nonnegative processing-time convention requires. Start times are natural numbers: Section 3
computes `B_j` from processing orders on integer data. -/
def IsFeasible (B : Fin I.n → ℕ) : Prop :=
  (∀ j, I.r j ≤ B j) ∧
    ∀ j k, j ≠ k →
      Disjoint (Set.Ico (B j) (B j + I.p j)) (Set.Ico (B k) (B k + I.p k))

/-- The completion time `C_j = B_j + p_{j1}`. -/
def C (B : Fin I.n → ℕ) (j : Fin I.n) : ℕ := B j + I.p j

/-- The lateness `L_j = C_j - d_j`, an integer (it may be negative). -/
def lateness (B : Fin I.n → ℕ) (j : Fin I.n) : ℤ := (I.C B j : ℤ) - I.d j

/-- `U_j = if C_j ≤ d_j then 0 else 1`. -/
def U (B : Fin I.n → ℕ) (j : Fin I.n) : ℕ := if I.C B j ≤ I.d j then 0 else 1

/-- The criterion `∑ w_j C_j = ∑_{j=1}^n w_j C_j` (p. 7). -/
def sumWC (B : Fin I.n → ℕ) : ℕ := ∑ j, I.w j * I.C B j

/-- The criterion `∑ w_j U_j = ∑_{j=1}^n w_j U_j` (p. 7): the total weight of the late jobs. -/
def sumWU (B : Fin I.n → ℕ) : ℕ := ∑ j, I.w j * I.U B j

/-- Default class: all jobs are available at time `0` (`r_j = 0` for every job, p. 6). -/
def AllReleasedAtZero : Prop := ∀ j, I.r j = 0

/-- The class element `r_n ≥ 0` (p. 7): there is at least one job, and every job except the last
one, `J_n` (index `n - 1`), has release date `0`; `J_n` may have any release date. -/
def OnlyLastReleased : Prop := 0 < I.n ∧ ∀ j : Fin I.n, (j : ℕ) + 1 < I.n → I.r j = 0

/-- The class element `w_j = 1` (p. 7): all weights equal one. -/
def UnitWeights : Prop := ∀ j, I.w j = 1

/-- The binary-coded data of an instance with threshold `y`, as a list of naturals: the number of
jobs `n`, then for each job `J_1, …, J_n` in turn its data `p_{j1}, w_j, r_j, d_j`, then `y`.
This list determines the instance and `y`. -/
def codeList (y : ℕ) : List ℕ :=
  I.n :: ((List.ofFn fun j : Fin I.n => [I.p j, I.w j, I.r j, I.d j]).flatten ++ [y])

end Instance

end SchedComplexity.OneMachine


