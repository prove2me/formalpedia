-- Prove2me | Definitions.Def_GreedWorks_OnlineList_Model
-- name    : GreedWorks_OnlineList_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:26.036768+00:00
-- url     : https://prove2.me/theorems/afbed540-a8a8-4ca7-b1f7-650146f762cd
-- title:
--   §2, pp. 4–6 — stochastic unrelated-machine instance and nonanticipatory comparator
-- statement:
--   Let $M$ be a finite machine set and $J=\{0,\ldots,n-1\}$ the jobs in presentation order. An **instance** specifies an eligibility relation $E\subseteq M\times J$, nonnegative weights $w_j$, a probability space $(\Omega,\mathbb P)$, and integer-valued processing times $P_{ij}$ for every pair. Every job has an eligible machine. Eligible pairs have finite second moments and means $\mu_{ij}=\mathbb E[P_{ij}]\ge1$; forbidden pairs represent the paper's infinite means. Different jobs' complete machine-time vectors are independent, while times for different machines of the same job may be dependent. The parameter $\Delta\ge0$ bounds $\operatorname{Var}(P_{ij})/\mu_{ij}^{2}$ on eligible pairs.
--
--   A **comparator policy** maps a complete processing-time table to one machine and one real start time per job. It is feasible if every job uses an eligible machine, begins at or after zero, and processing intervals on a machine do not overlap. Nonanticipation means that changing unobserved processing times cannot change any decisions already made by time $t$: completed jobs retain their observed durations, running jobs remain unfinished, and the choices and start times of all jobs started by $t$ are fixed. A comparator is admissible if it is feasible for every realization, nonanticipatory, and each realized completion time is integrable. Its cost is
--
--   $$\mathbb E\!\left[\sum_{j\in J}w_j C_j^\Pi\right].$$
--
--   These definitions specify the unrestricted benchmark used throughout the mission. **Formalization Note** At $n=0$ the structure also permits an empty machine set; the goal theorems supply a nonempty machine set. The processing times stored for forbidden pairs are placeholders and play no role in costs or feasibility. Zero-duration jobs occupy no processing interval; the paper does not state $w_j\ge0$ explicitly, but the analysis requires it. Completion-time integrability prevents a nonintegrable Lean integral from taking a default zero value.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, pp. 4–6, §2 and §2.1

import Mathlib

namespace GreedWorks.OnlineList

open MeasureTheory ProbabilityTheory

/-- A stochastic unrelated-machine instance in the online-list model of §2.  `Fin n` is
the order in which jobs are presented.  Ineligible pairs represent infinite means. -/
structure StochasticInstance (M : Type*) [Fintype M] (n : ℕ)
    (Ω : Type*) [MeasurableSpace Ω] where
  Pr : Measure Ω
  probability : IsProbabilityMeasure Pr
  P : M → Fin n → Ω → ℕ
  measurable : ∀ i j, Measurable (P i j)
  eligible : M → Fin n → Prop
  memLp : ∀ i j, eligible i j → MemLp (fun ω => (P i j ω : ℝ)) 2 Pr
  hasMachine : ∀ j, ∃ i, eligible i j
  meanAtLeastOne : ∀ i j, eligible i j → 1 ≤ ∫ ω, (P i j ω : ℝ) ∂Pr
  independentJobs : iIndepFun (fun j ω => fun i => (P i j ω : ℝ)) Pr
  weight : Fin n → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  Delta : ℝ
  Delta_nonneg : 0 ≤ Delta
  cvBound : ∀ i j, eligible i j →
    variance (fun ω => (P i j ω : ℝ)) Pr ≤
      Delta * (∫ ω, (P i j ω : ℝ) ∂Pr) ^ 2

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The finite mean of an eligible processing-time distribution. -/
noncomputable def mean (I : StochasticInstance M n Ω) (i : M) (j : Fin n) : ℝ :=
  ∫ ω, (I.P i j ω : ℝ) ∂I.Pr

/-- The processing-time table is a realization, with arbitrary entries on forbidden pairs. -/
abbrev Realization (M : Type*) (n : ℕ) := M → Fin n → ℕ

/-- A policy chooses both a machine and a real start time from a realization. -/
abbrev Policy (M : Type*) (n : ℕ) :=
  Realization M n → (Fin n → M) × (Fin n → ℝ)

def machine (pol : Policy M n) (p : Realization M n) (j : Fin n) : M := (pol p).1 j
def start (pol : Policy M n) (p : Realization M n) (j : Fin n) : ℝ := (pol p).2 j

/-- Completion time for a policy on a specified realization. -/
def completion (pol : Policy M n) (p : Realization M n) (j : Fin n) : ℝ :=
  start pol p j + (p (machine pol p j) j : ℝ)

/-- Every job uses an eligible machine, begins at or after zero, and jobs on the same
machine have disjoint half-open processing intervals.  Zero-length jobs occupy no time. -/
def IsFeasible (I : StochasticInstance M n Ω) (pol : Policy M n) : Prop :=
  ∀ p : Realization M n,
    (∀ j, I.eligible (machine pol p j) j) ∧
    (∀ j, 0 ≤ start pol p j) ∧
    (∀ j k, j ≠ k → machine pol p j = machine pol p k →
      p (machine pol p j) j = 0 ∨ p (machine pol p k) k = 0 ∨
        completion pol p j ≤ start pol p k ∨ completion pol p k ≤ start pol p j)

/-- Decisions by time `t` are invariant when a second realization agrees on the
processing times already observed: completed jobs have the same duration, and jobs
running at `t` remain unfinished at `t`.  Unstarted jobs and unchosen machines may vary. -/
def IsNonanticipatory (pol : Policy M n) : Prop :=
  ∀ (t : ℝ) (p p' : Realization M n),
    (∀ j, start pol p j ≤ t →
      (completion pol p j ≤ t → p' (machine pol p j) j = p (machine pol p j) j) ∧
      (t < completion pol p j → t < start pol p j + (p' (machine pol p j) j : ℝ))) →
    ∀ j, (start pol p j ≤ t ↔ start pol p' j ≤ t) ∧
      (start pol p j ≤ t →
        start pol p' j = start pol p j ∧ machine pol p' j = machine pol p j)

/-- The comparator class knows the distributions and all jobs but not future processing
time realizations.  Integrability prevents Lean's zero value for a nonintegrable integral. -/
def IsAdmissible (I : StochasticInstance M n Ω) (pol : Policy M n) : Prop :=
  IsFeasible I pol ∧ IsNonanticipatory pol ∧
    ∀ j, Integrable (fun ω => completion pol (fun i k => I.P i k ω) j) I.Pr

/-- Expected total weighted completion time of an admissible comparator. -/
noncomputable def comparatorCost (I : StochasticInstance M n Ω) (pol : Policy M n) : ℝ :=
  ∫ ω, ∑ j : Fin n, I.weight j * completion pol (fun i k => I.P i k ω) j ∂I.Pr

end GreedWorks.OnlineList


