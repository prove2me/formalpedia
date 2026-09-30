-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
-- name    : SingleMachineSched_AlphaJSched_LPSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:15:25.82699+00:00
-- url     : https://prove2.me/theorems/f4fb2ca6-f43e-4e29-a7b2-131899f1f1a4
-- title:
--   The LP schedule of $1|r_j|\sum w_jC_j$ and the mean busy times $M^{LP}_j$
-- statement:
--   A set of $n$ jobs, indexed $0,1,\dots,n-1$, is to be processed on a single machine. Job $j$ has an integral processing time $p_j$ and an integral release date $r_j\ge 0$.
--
--   The **LP schedule** is the preemptive schedule that, at every point in time, processes the available (released and unfinished) job of smallest index; a newly released job of smaller index preempts the job in process. Because all data are integral, every release and every completion happens at an integer time, so the LP schedule is described slot by slot: in each unit slot $[\tau,\tau+1)$, $\tau=0,1,2,\dots$, it processes the smallest-index job $j$ with $r_j\le\tau$ that still has work left, or it idles if there is none. This file defines
--
--   1. $\mathrm{rem}_\tau(j)$, the work of job $j$ left at the start of slot $\tau$ ($\mathrm{rem}_0(j)=p_j$, decreased by one in every slot in which $j$ runs);
--   2. the job run in slot $\tau$ (or "idle");
--   3. the set $A^{LP}_j\subseteq\mathbb R$ of times at which the LP schedule processes $j$, the union of its slots;
--   4. the **mean busy time** of job $j$ in a preemptive schedule with processing sets $A$,
--   $$M_j=\frac1{p_j}\int_{A_j} t\,dt,$$
--   the average time at which the machine processes $j$; and $M^{LP}_j$, the mean busy time of $j$ in the LP schedule.
--
--   When the jobs are indexed in nonincreasing order of $w_j/p_j$, with ties broken by index, as the paper assumes throughout, the smallest-index rule is the paper's rule "schedule the available job with the highest ratio $w_j/p_j$". The LP schedule is the object from which every schedule of this mission is derived.
--
--   **Formalization Note.** Jobs are `Fin n` (0-based) and $p$, $r$ are natural numbers. The ordering by $w_j/p_j$ is not part of the definition: it is the hypothesis `hsort` of every theorem that speaks about the LP schedule. The paper's indicator function $I_j$ is the indicator of $A^{LP}_j$, and its horizon $T$ is implicit because $A^{LP}_j$ is a finite union of slots. That $A^{LP}_j$ is a preemptive schedule (disjoint, measure $p_j$, after $r_j$) is a fact about the definition, not part of it.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 165 (model), p. 169 (LP schedule), p. 171 (mean busy time)

import Mathlib

namespace SingleMachineSched.AlphaJSched

open MeasureTheory

/-- The job the smallest-index preemptive rule runs in the unit slot `[τ, τ + 1)` when `rem j`
units of work of job `j` are left: the smallest index among released, unfinished jobs, or
`none` (idle) if there is none. -/
def lpPick {n : ℕ} (r : Fin n → ℕ) (τ : ℕ) (rem : Fin n → ℕ) : Option (Fin n) :=
  if h : (Finset.univ.filter (fun j => r j ≤ τ ∧ 0 < rem j)).Nonempty then
    some ((Finset.univ.filter (fun j => r j ≤ τ ∧ 0 < rem j)).min' h)
  else none

/-- Work left of each job at the start of slot `τ` in the LP schedule. -/
def lpRemaining {n : ℕ} (p r : Fin n → ℕ) : ℕ → Fin n → ℕ
  | 0 => p
  | τ + 1 => fun j =>
      if lpPick r τ (lpRemaining p r τ) = some j then lpRemaining p r τ j - 1
      else lpRemaining p r τ j

/-- The job processed in slot `[τ, τ + 1)` by the LP schedule (`none` = machine idle). -/
def lpRun {n : ℕ} (p r : Fin n → ℕ) (τ : ℕ) : Option (Fin n) :=
  lpPick r τ (lpRemaining p r τ)

/-- The set of times at which the LP schedule processes job `j`. -/
def lpSet {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Set ℝ :=
  ⋃ (τ : ℕ) (_ : lpRun p r τ = some j), Set.Ico (τ : ℝ) (τ + 1)

/-- The mean busy time `M_j = (1/p_j) ∫ I_j(t) t dt` of job `j` in a preemptive schedule given by
its processing sets `A` (p. 171): the average time at which the machine processes `j`. -/
noncomputable def meanBusyTime {n : ℕ} (p : Fin n → ℕ) (A : Fin n → Set ℝ) (j : Fin n) : ℝ :=
  (1 / (p j : ℝ)) * ∫ t in A j, t

/-- `M^LP_j`, the mean busy time of job `j` in the LP schedule. -/
noncomputable def mLP {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : ℝ :=
  meanBusyTime p (lpSet p r) j

end SingleMachineSched.AlphaJSched


