-- Prove2me | Definitions.Def_SingleMachineSched_Shared_PreemptiveSchedule
-- name    : SingleMachineSched_Shared_PreemptiveSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:44:23.075022+00:00
-- url     : https://prove2.me/theorems/3e499e2b-de54-437c-8ad9-63fd9e77cd78
-- title:
--   Preemptive single-machine schedules and the mean busy time $M_j$
-- statement:
--   A set $N$ of $n$ jobs is to be processed on a single machine. Job $j$ has an integral processing time $p_j > 0$ and an integral release date $r_j \ge 0$.
--
--   A **preemptive schedule** assigns to every job $j$ a set $A_j \subseteq \mathbb R$ of times at which the machine processes $j$. It must satisfy:
--
--   1. each $A_j$ is Lebesgue measurable and bounded;
--   2. $A_j \subseteq [r_j, \infty)$, so no job is processed before its release date;
--   3. $A_j$ has Lebesgue measure exactly $p_j$, so each job receives its full processing time;
--   4. the sets $A_j$ are pairwise disjoint, so the machine processes at most one job at a time.
--
--   The paper describes the same object through the indicator function $I_j$ of $A_j$. The **mean busy time** of job $j$ is the average time at which it is processed,
--
--   $$M_j = \frac{1}{p_j} \int_{A_j} t \, dt .$$
--
--   Mean busy times are the variables of the relaxation (R), and Lemma 2.4 shows that every preemptive schedule yields a feasible point of (R).
--
--   It serves two missions of the series: `01-lp-relaxations` (p. 171, PDF p. 7, preemptive schedules and mean busy time; the hypothesis of Lemma 2.4, p. 172, PDF p. 8; $M^{LP}_j$ of the LP schedule, used in Theorem 2.5, p. 173, PDF p. 9) and `02-alpha-schedule` (p. 171, PDF p. 7; $M^{LP}_j$ of the LP schedule, used in Theorem 2.5, p. 173, PDF p. 9). It is reviewed once for both.
--
--   **Formalization Note** Jobs are indexed by `Fin n` (0-based), and processing times and release dates are natural numbers. The paper's convention that a job, once started, runs for a positive amount of time is a regularity convention on indicator functions; measurable sets make it unnecessary. The paper integrates up to a horizon $T$; boundedness of each $A_j$ plays that role and makes the integral finite. `meanBusyTime` is defined for any family of sets; it is the paper's $M_j$ when that family is a preemptive schedule.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 165 (model) and p. 171 (preemptive schedules, mean busy time); used on p. 172 (Lemma 2.4) and p. 173 (Theorem 2.5)

import Mathlib

namespace SingleMachineSched.Shared

open MeasureTheory

/-- A preemptive schedule of the jobs `Fin n` on one machine (Goemans et al. 2002, p. 171).
`A j ⊆ ℝ` is the set of times at which the machine processes job `j` (the paper's indicator
function `I_j` is the indicator of `A j`). The schedule respects release dates, processes each
job for exactly `p j` time units, processes at most one job at a time, and ends in finite time. -/
structure IsPreemptiveSchedule {n : ℕ} (p r : Fin n → ℕ) (A : Fin n → Set ℝ) : Prop where
  measurable : ∀ j, MeasurableSet (A j)
  release : ∀ j, A j ⊆ Set.Ici (r j : ℝ)
  volume_eq : ∀ j, volume (A j) = (p j : ENNReal)
  disjoint : Pairwise (Function.onFun Disjoint A)
  bounded : ∀ j, Bornology.IsBounded (A j)

/-- The mean busy time `M_j = (1/p_j) ∫ I_j(t) t dt` of job `j` in the schedule `A`
(p. 171): the average time at which the machine processes `j`. -/
noncomputable def meanBusyTime {n : ℕ} (p : Fin n → ℕ) (A : Fin n → Set ℝ) (j : Fin n) : ℝ :=
  (1 / (p j : ℝ)) * ∫ t in A j, t

end SingleMachineSched.Shared


