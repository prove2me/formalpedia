-- Prove2me | Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList
-- name    : AvgCompletionSched_ParallelRelease_DelayList
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:52:38.447839+00:00
-- url     : https://prove2.me/theorems/dfb459fc-cc33-4262-98e3-82e490d076a8
-- title:
--   The continuous-time Delay List algorithm with parameter $\beta$, without precedence constraints
-- statement:
--   This file defines the runs of the algorithm Delay List of §4.1 of Chekuri, Motwani, Natarajan and Stein, for jobs with release dates and no precedence constraints (so a job is *ready* exactly from its release date on), in continuous time.
--
--   Fix a parameter $\beta$ and a list $\pi$ of the jobs; write $\mathrm{pos}(j)$ for the position of $J_j$ in the list. A run consists of start times $S_j$, machines $M_j$, the order in which the algorithm schedules the jobs (several jobs may be scheduled at the same instant, one after the other), and for each job a window $(\tau_j,S_j)$ from which it takes its *charged idle time*.
--
--   **Idle time.** At time $t$ the number of idle machines is $m-\#\{k: S_k\le t<S_k+p_k\}$; idle time is measured in machine $\times$ time. The idle time **charged** to $J_j$ is the idle time in its window $(\tau_j,S_j)$ that no job scheduled before $J_j$ has already charged. The **uncharged idle time** available at a given moment is the idle time in $[0,t)$ outside the windows of the jobs already scheduled.
--
--   A run is a **Delay List schedule** if:
--
--   1. **Feasibility.** $S_j\ge r_j$; jobs are scheduled in nondecreasing order of start time; a job is put on a machine on which every job scheduled earlier has finished.
--   2. **The two cases.** When $J_j$ is scheduled, either
--       - *(case 1, in order)* $J_j$ is the first job of the list among the jobs not yet scheduled, and it is charged all uncharged idle time in $(r_j,S_j)$; or
--       - *(case 2, out of order)* the first unscheduled job of the list is not ready at $S_j$, $J_j$ is the first ready unscheduled job of the list, at least $\beta p_j$ uncharged idle time has accumulated, and $J_j$ is charged exactly $\beta p_j$ of it, taken from the most recent uncharged idle time.
--   3. **No delay.** At every time $t\ge 0$ at which some machine is idle, once all jobs starting at or before $t$ have been scheduled, neither case applies: the first unscheduled job of the list is not ready at $t$, and the first ready unscheduled job $J_k$ (if any) has less than $\beta p_k$ uncharged idle time available. In particular a job scheduled out of order starts at the first instant at which $\beta p_k$ units of uncharged idle time have accumulated.
--
--   This is the conversion algorithm that turns a one-machine schedule, read as a list, into an $m$-machine schedule; Theorem 4.9 bounds the completion time of every job it produces.
--
--   **Formalization Note** The paper describes the algorithm in discrete time and states that the restriction to integer data "can be removed without much difficulty"; in the proof of Fact 4.6 it adopts the continuous rule that a job is scheduled "at the first time instant when at least $\beta p_i$ units of uncharged idle time have accumulated". This file formalizes that continuous-time version. The paper does not say where on the time axis a case-2 charge sits; this file takes it from the most recent uncharged idle time (the charged window is $(\tau_j,S_j)$ with $0\le\tau_j\le S_j$), which also makes case 1 and case 2 charges both "all uncharged idle time in a window ending at $S_j$". The predicate does not assume $\beta>0$ or $m\ge 2$; the theorems that use it do.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 158–159 §4.1 (Delay List, Definitions 4.2–4.3, cases 1–3), p. 159 proof of Fact 4.6 (continuous-time rule)

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

variable {n m : ℕ}

/-- The data of a run of the continuous-time algorithm Delay List (§4.1, pp. 158–159) on an
instance without precedence constraints: start times `S`, machines `M`, the left end `τ j` of the
time window from which job `j` takes its charged idle time, and the order `ev` in which the
algorithm schedules the jobs (`ev a` is the `a`-th job scheduled; several jobs may be scheduled at
the same instant, one after the other). -/
structure DelayListRun (I : Instance n m) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  /-- left end of the charge window of each job -/
  τ : Fin n → ℝ
  /-- scheduling order: `ev a` is the `a`-th job the algorithm schedules -/
  ev : Fin n ≃ Fin n

namespace DelayListRun

variable {I : Instance n m} (D : DelayListRun I)

/-- Completion time `C^D_j = S_j + p_j`. -/
def C (j : Fin n) : ℝ := D.S j + I.p j

/-- Job `k` is scheduled by the algorithm before job `j`. -/
def Before (k j : Fin n) : Prop := D.ev.symm k < D.ev.symm j

/-- Number of idle machines at time `t`: `m` minus the number of jobs running at `t`. -/
noncomputable def idle (t : ℝ) : ℝ :=
  (m : ℝ) - ((Finset.univ.filter fun k => D.S k ≤ t ∧ t < D.S k + I.p k).card : ℝ)

/-- The charge window of job `j`: the open interval `(τ j, S j)`. -/
def window (j : Fin n) : Set ℝ := Set.Ioo (D.τ j) (D.S j)

/-- Idle time (machine × time) charged to job `j`: the idle time in its window that no job
scheduled before `j` has already charged. -/
noncomputable def charge (j : Fin n) : ℝ :=
  ∫ t in D.window j \ ⋃ k ∈ {k | D.Before k j}, D.window k, D.idle t

/-- Uncharged idle time accumulated during `[0, S j)` at the moment `j` is scheduled, i.e. after
the charges of the jobs scheduled before `j`. -/
noncomputable def unchargedAt (j : Fin n) : ℝ :=
  ∫ t in Set.Ico 0 (D.S j) \ ⋃ k ∈ {k | D.Before k j}, D.window k, D.idle t

/-- Uncharged idle time accumulated during `[0, t)` once every job starting at or before `t` has
been scheduled and charged. -/
noncomputable def unchargedAfter (t : ℝ) : ℝ :=
  ∫ s in Set.Ico 0 t \ ⋃ k ∈ {k | D.S k ≤ t}, D.window k, D.idle s

end DelayListRun

/-- `D` is a run of the continuous-time Delay List algorithm with parameter `β` on the list `π`
(`π k` is the `k`-th job of the list), for jobs without precedence constraints, so that a job is
ready exactly from its release date on (§4.1, pp. 158–159, with the continuous-time rule of the
proof of Fact 4.6, p. 159). Writing `pos j` for the list position of `j`:

1. (feasibility) every job starts no earlier than its release date, on a machine on which every
   job scheduled earlier has finished; jobs are scheduled in nondecreasing order of start time;
2. (the two scheduling cases) each job `j`, when it is scheduled, is either
   * *case 1*: the first job of the list among the jobs not yet scheduled; it is charged all
     uncharged idle time in `(r j, S j)` (`τ j = r j`); or
   * *case 2*: the first job of the list among the unscheduled jobs is not ready at `S j`, `j` is
     the first ready unscheduled job of the list, at least `β p j` uncharged idle time has
     accumulated, and `j` is charged exactly `β p j` of it, taken from the most recent uncharged
     idle time (the window `(τ j, S j)` with `0 ≤ τ j ≤ S j`);
3. (no delay) at every time `t ≥ 0` at which some machine is idle, once all jobs starting at or
   before `t` are scheduled, neither case applies: the first unscheduled job of the list is not
   ready, and the first ready unscheduled job `k` (if any) has less than `β p k` uncharged idle
   time available. -/
def IsDelayListSchedule (I : Instance n m) (π : Fin n ≃ Fin n) (β : ℝ) (D : DelayListRun I) :
    Prop :=
  -- feasibility
  (∀ j, I.r j ≤ D.S j) ∧
  (∀ j k, D.Before k j → D.S k ≤ D.S j) ∧
  (∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j) ∧
  -- the two scheduling cases
  (∀ j,
    ((∀ k, ¬ D.Before k j → π.symm j ≤ π.symm k) ∧ D.τ j = I.r j) ∨
    ((∀ h, ¬ D.Before h j → (∀ k, ¬ D.Before k j → π.symm h ≤ π.symm k) → D.S j < I.r h) ∧
      (∀ k, ¬ D.Before k j → I.r k ≤ D.S j → π.symm j ≤ π.symm k) ∧
      β * I.p j ≤ D.unchargedAt j ∧
      0 ≤ D.τ j ∧ D.τ j ≤ D.S j ∧
      D.charge j = β * I.p j)) ∧
  -- no delay
  (∀ t, 0 ≤ t → (∃ μ : Fin m, ∀ k, D.M k = μ → ¬ (D.S k ≤ t ∧ t < D.S k + I.p k)) →
    (∀ h, t < D.S h → (∀ k, t < D.S k → π.symm h ≤ π.symm k) → t < I.r h) ∧
    (∀ k, t < D.S k → I.r k ≤ t → (∀ l, t < D.S l → I.r l ≤ t → π.symm k ≤ π.symm l) →
      D.unchargedAfter t < β * I.p k))

end AvgCompletionSched.ParallelRelease


