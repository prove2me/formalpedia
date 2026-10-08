-- Prove2me | Definitions.Def_EmmonsTardiness_SPT_Model
-- name    : EmmonsTardiness_SPT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:09:35.885222+00:00
-- url     : https://prove2.me/theorems/504b65e1-abd4-4351-b63b-aa5a54cfd9a4
-- title:
--   Tardiness, total tardiness, optimal schedules, precedence, SPT indexing and the SPT schedule
-- statement:
--   This file sets up the one-machine total-tardiness model of Emmons (1969).
--
--   A finite set $J$ of jobs is to be processed on one machine. All jobs are available at time $0$; job $i$ has a processing time $p_i$ and a due date $d_i$ (real numbers). A **schedule** of $J$ is an ordering of the jobs of $J$, i.e. a list without repetitions whose entries are exactly the jobs of $J$. The machine processes the jobs of a schedule one after another from time $0$ without idle time, so a job completes at the sum of the processing times of the jobs up to and including it in the schedule.
--
--   1. The **tardiness** of job $i$ in a schedule is $T_i = \max(0, C_i - d_i)$, where $C_i$ is its completion time.
--   2. The **total tardiness** of a schedule is $T = \sum_{i\in J} T_i$.
--   3. A schedule $l$ of $J$ is **optimal** if its total tardiness is at most that of every schedule of $J$:
--   $$T(l) \le T(l') \quad \text{for every schedule } l' \text{ of } J.$$
--   4. Job $a$ **precedes** job $b$ in a schedule if $a$ occurs at an earlier position than $b$.
--   5. The jobs are **SPT-indexed** if they are indexed in order of nondecreasing processing times and, in case of equality, of nondecreasing due dates: $j<k$ implies $p_j<p_k$, or $p_j=p_k$ and $d_j\le d_k$.
--   6. The **SPT schedule** processes the jobs in increasing index order; for SPT-indexed jobs this is shortest-processing-time order with ties broken by earliest due date.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Jobs are elements of a type $\iota$ whose linear order is the paper's job index, and $J$ is a `Finset ι`, so that removing a job keeps the remaining labels. Schedules and completion times are the published definitions `MooreLateJobs.Shared.IsSchedule` and `MooreLateJobs.Shared.completionTime` (Moore 1968), with Emmons's $p$ passed as Moore's processing-time argument $t$. "Precedes" compares first-occurrence indices (`List.idxOf`), and the SPT schedule is `J.sort (· ≤ ·)`.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 701 (introduction: model, lateness, tardiness, total tardiness), p. 703 (indexing convention of §Some theorems on ordering jobs to minimize total tardiness; notation j←k of §Existential versus universal properties)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Tardiness `T_i = max(0, C_i − d_i)` of job `i` in the sequence `l` (Emmons 1969, p. 701):
`C_i = Shared.completionTime p l i` is the completion time of `i` when the jobs of `l` are
processed in order from time `0` without idle time, `p` being the processing times and `d` the
due dates. -/
noncomputable def tardiness {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (l : List ι) (i : ι) : ℝ :=
  max 0 (Shared.completionTime p l i - d i)

/-- Total tardiness `T = Σ_{i ∈ J} T_i` of the sequence `l` over the job set `J` (p. 701). -/
noncomputable def totalTardiness {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (l : List ι) : ℝ :=
  ∑ i ∈ J, tardiness p d l i

/-- `l` is an optimal schedule of `J`: it is a schedule of `J` (a duplicate-free list whose
elements are exactly the jobs of `J`) and its total tardiness is at most that of every schedule
of `J`. -/
def IsOptimal {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι) (l : List ι) : Prop :=
  Shared.IsSchedule J l ∧
    ∀ l' : List ι, Shared.IsSchedule J l' → totalTardiness p d J l ≤ totalTardiness p d J l'

/-- Job `a` precedes job `b` in the sequence `l`: `a` occurs at an earlier position than `b`. -/
def Precedes {ι : Type*} [DecidableEq ι] (l : List ι) (a b : ι) : Prop :=
  l.idxOf a < l.idxOf b

/-- The indexing convention of p. 703: jobs are indexed (by the linear order of `ι`) in order of
nondecreasing processing times and, in case of equality, of nondecreasing due dates, i.e.
`j < k` implies `p_j < p_k`, or `p_j = p_k` and `d_j ≤ d_k`. -/
def IsSPTIndexed {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, ∀ k ∈ J, i < k → p i < p k ∨ (p i = p k ∧ d i ≤ d k)

/-- The SPT schedule: the jobs of `J` in increasing index order. Under `IsSPTIndexed p d J` this
is shortest-processing-time order with ties broken by earliest due date. -/
def sptSchedule {ι : Type*} [LinearOrder ι] (J : Finset ι) : List ι :=
  J.sort (· ≤ ·)

end EmmonsTardiness.SPT


