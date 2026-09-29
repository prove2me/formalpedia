-- Prove2me | Definitions.Def_AvgCompletionSched_DelayList_Algorithm
-- name    : AvgCompletionSched_DelayList_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:00:08.854563+00:00
-- url     : https://prove2.me/theorems/b47f19fb-dc1f-4c11-b1e5-cb3b7da3a9a1
-- title:
--   The conversion algorithm Delay List (continuous time) with idle-time charging
-- statement:
--   This file defines the runs of the algorithm Delay List of §4.1, in the continuous-time form the paper uses in the proof of Fact 4.6.
--
--   Fix $m$ machines, a parameter $\beta>0$ and a list $\pi$ of the jobs. A job is **ready** at time $t$ if $r_j\le t$ and every predecessor $i\prec j$ has completed by $t$; the **ready time** $q^m_j$ (Definition 4.2) is $r_j$ if $j$ has no predecessors and $\max\{\max_{i\prec j}C^m_i,\,r_j\}$ otherwise. The **list** at a moment is the set of jobs not yet scheduled, ordered by $\pi$; its first job is the **head**. The number of **idle** machines at time $t$ is $m$ minus the number of jobs running at $t$; idle time is measured in machines $\times$ time.
--
--   A run consists of start times $s^m_j$, machines, an order in which the jobs are scheduled (several jobs may be scheduled at the same instant, one after the other), and for each job $j$ a window $(\tau_j,s^m_j)$: the idle time charged to $j$ is the idle time at the times of its window that were not already in the window of a job scheduled before $j$. A run is a **Delay List schedule** if:
--
--   1. jobs are scheduled in nondecreasing order of start time, each on a machine on which every job scheduled earlier has finished;
--   2. each job $j$, when it is scheduled at time $t=s^m_j$, is scheduled by one of the paper's two cases:
--      - **case 1:** $j$ is the head of the list and is ready at $t$; it is charged all uncharged idle time in $(q^m_j,s^m_j)$;
--      - **case 2:** the head of the list is not ready at $t$, $j$ is ready and is the first job of the list among the ready jobs, at least $\beta p_j$ units of uncharged idle time have accumulated among all machines, and $j$ is charged exactly $\beta p_j$ units of it, taken from the most recent uncharged idle time;
--   3. **(case 3: no delay)** at every time $t\ge 0$ at which a machine is idle, after all jobs starting at or before $t$ have been scheduled, the head of the list is not ready, and the first ready job $k$ of the list (if any) has less than $\beta p_k$ uncharged idle time available. Thus a ready head is scheduled at once, and an out-of-order job is scheduled at the first instant at which $\beta p_k$ units of uncharged idle time have accumulated.
--
--   The approximation guarantees of the mission hold for every run satisfying these rules, whatever the tie-breaking among machines and among simultaneous events.
--
--   **Formalization Note** The paper describes the algorithm in discrete time "for ease of exposition" and then states that the discrete version may charge too much idle time, which is "easily fixed in the continuous case where we schedule $J_i$ at the first time instant when at least $\beta p_i$ units of uncharged idle time have accumulated" (proof of Fact 4.6); the continuous version is formalized. The paper does not say which uncharged idle time a case-2 charge consumes; the formalization takes the most recent one, charged by whole time slices (all idle machines at a time). Idle time is a Bochner integral of the bounded step function "number of idle machines" over bounded sets of times, so it is never a junk value.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 158–159 §4.1 (Definition 4.2, cases 1–3, footnote 2), p. 159 (proof of Fact 4.6, continuous-time rule)

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model

namespace AvgCompletionSched.DelayList

open MeasureTheory

variable {n : ℕ}

/-- The data of a run of the continuous-time algorithm Delay List (§4.1, pp. 158–159) on `m`
machines: start times `S`, machines `M`, the left end `τ j` of the time window `(τ j, S j)` from
which job `j` takes the idle time charged to it, and the order `ev` in which the algorithm
schedules the jobs (`ev a` is the `a`-th job scheduled; several jobs may be scheduled at the same
instant, one after the other). -/
structure DelayListRun (I : Instance n) (m : ℕ) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  /-- left end of the charge window of each job -/
  τ : Fin n → ℝ
  /-- scheduling order: `ev a` is the `a`-th job the algorithm schedules -/
  ev : Fin n ≃ Fin n

namespace DelayListRun

variable {I : Instance n} {m : ℕ} (D : DelayListRun I m)

/-- Completion time `C^m_j = s^m_j + p_j`. -/
def C (j : Fin n) : ℝ := D.S j + I.p j

/-- Sum of weighted completion times `C^m = ∑_j w_j C^m_j` of the run. -/
noncomputable def wct : ℝ := ∑ j, I.w j * D.C j

/-- Job `k` is scheduled by the algorithm before job `j`. -/
def Before (k j : Fin n) : Prop := D.ev.symm k < D.ev.symm j

/-- Job `j` is *ready* at time `t` (p. 158): it has been released and all its predecessors are
done. -/
def Ready (t : ℝ) (j : Fin n) : Prop := I.r j ≤ t ∧ ∀ i, I.prec i j → D.C i ≤ t

/-- The time `q^m_j` at which job `j` becomes ready (Definition 4.2, p. 158): its release date if
it has no predecessors, otherwise the maximum of its release date and the completion times of its
predecessors. -/
noncomputable def q (j : Fin n) : ℝ :=
  if h : (I.preds j).Nonempty then max ((I.preds j).sup' h D.C) (I.r j) else I.r j

open Classical in
/-- Number of idle machines at time `t`: `m` minus the number of jobs running at `t`. -/
noncomputable def idle (t : ℝ) : ℝ :=
  (m : ℝ) - ((Finset.univ.filter fun k => D.S k ≤ t ∧ t < D.S k + I.p k).card : ℝ)

/-- Some machine is idle at time `t`: no job assigned to it runs at `t`. -/
def IdleMachineAt (t : ℝ) : Prop :=
  ∃ μ : Fin m, ∀ k, D.M k = μ → ¬ (D.S k ≤ t ∧ t < D.S k + I.p k)

/-- The charge window of job `j`: the open interval `(τ j, S j)`. -/
def window (j : Fin n) : Set ℝ := Set.Ioo (D.τ j) (D.S j)

/-- The times whose idle machines are charged to job `j`: its window minus the windows of the
jobs scheduled before it (whose idle time was already charged). -/
def chargedSet (j : Fin n) : Set ℝ :=
  D.window j \ ⋃ k ∈ {k | D.Before k j}, D.window k

/-- Idle time (machines × time) charged to job `j`. -/
noncomputable def charge (j : Fin n) : ℝ :=
  ∫ t in D.chargedSet j, D.idle t

/-- Uncharged idle time among all machines accumulated during `[0, S j)` at the moment `j` is
scheduled, i.e. after the charges of the jobs scheduled before `j`. -/
noncomputable def unchargedAt (j : Fin n) : ℝ :=
  ∫ t in Set.Ico 0 (D.S j) \ ⋃ k ∈ {k | D.Before k j}, D.window k, D.idle t

/-- Uncharged idle time among all machines accumulated during `[0, t)` once every job starting at
or before `t` has been scheduled and charged. -/
noncomputable def unchargedAfter (t : ℝ) : ℝ :=
  ∫ s in Set.Ico 0 t \ ⋃ k ∈ {k | D.S k ≤ t}, D.window k, D.idle s

end DelayListRun

/-- `D` is a run of the continuous-time Delay List algorithm with parameter `β` on `m` machines
using the list `π` (`π k` is the `k`-th job of the list) (§4.1, pp. 158–159, with the
continuous-time rule of the proof of Fact 4.6, p. 159). "The list" at a given moment consists of
the jobs not yet scheduled; its first job is the *head*.

1. (bookkeeping) jobs are scheduled in nondecreasing order of start time, and each job is put on
   a machine on which every job scheduled earlier has finished (an idle machine);
2. (the two scheduling cases) each job `j`, when it is scheduled at time `S j`, is either
   * *case 1*: the head of the list, and ready at `S j`; it is charged all uncharged idle time in
     `(q^m_j, S j)` (`τ j = q^m_j`); or
   * *case 2*: the head of the list is not ready at `S j`, `j` is ready and is the first job of the
     list among the ready ones, at least `β p j` uncharged idle time has accumulated among all
     machines, and `j` is charged exactly `β p j` of it, taken from the most recent uncharged idle
     time (the window `(τ j, S j)` with `0 ≤ τ j ≤ S j`);
3. (case 3, no delay) at every time `t ≥ 0` at which some machine is idle, once all jobs starting
   at or before `t` are scheduled, neither case applies: the head of the list is not ready, and the
   first ready job `k` of the list (if any) has less than `β p k` uncharged idle time available;
   that is, a ready head is scheduled at once, and an out-of-order job is scheduled at the first
   instant at which `β p k` units of uncharged idle time have accumulated. -/
def IsDelayListSchedule (I : Instance n) (m : ℕ) (π : Fin n ≃ Fin n) (β : ℝ)
    (D : DelayListRun I m) : Prop :=
  -- bookkeeping
  (∀ j k, D.Before k j → D.S k ≤ D.S j) ∧
  (∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j) ∧
  -- the two scheduling cases
  (∀ j,
    ((∀ k, ¬ D.Before k j → π.symm j ≤ π.symm k) ∧ D.Ready (D.S j) j ∧ D.τ j = D.q j) ∨
    ((∀ h, ¬ D.Before h j → (∀ k, ¬ D.Before k j → π.symm h ≤ π.symm k) →
        ¬ D.Ready (D.S j) h) ∧
      D.Ready (D.S j) j ∧
      (∀ k, ¬ D.Before k j → D.Ready (D.S j) k → π.symm j ≤ π.symm k) ∧
      β * I.p j ≤ D.unchargedAt j ∧
      0 ≤ D.τ j ∧ D.τ j ≤ D.S j ∧
      D.charge j = β * I.p j)) ∧
  -- no delay
  (∀ t, 0 ≤ t → D.IdleMachineAt t →
    (∀ h, t < D.S h → (∀ k, t < D.S k → π.symm h ≤ π.symm k) → ¬ D.Ready t h) ∧
    (∀ k, t < D.S k → D.Ready t k → (∀ l, t < D.S l → D.Ready t l → π.symm k ≤ π.symm l) →
      D.unchargedAfter t < β * I.p k))

end AvgCompletionSched.DelayList


