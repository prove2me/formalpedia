-- Prove2me | Definitions.Def_TwoAgentSched_IsSketchSuffix
-- name    : TwoAgentSched_IsSketchSuffix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:46:46.973503+00:00
-- url     : https://prove2.me/theorems/1abb689f-851a-474c-98af-f8e27fc4fb69
-- title:
--   Runs of the §4 sketch of Lawler's algorithm
-- statement:
--   The §4 sketch builds a schedule backwards: at each step it selects, among the unscheduled jobs, the job to be scheduled last. Let $\rho$ be the jobs fixed so far, in processing order, and let
--   $$
--   \bar\tau = \sum_{j \notin \rho} p_j
--   $$
--   be the sum of the processing times of the unscheduled jobs. A legal step puts in front of $\rho$ (that is, last among the unscheduled jobs, ending at $\bar\tau$)
--
--   1. any unscheduled B-job $J^B_k$ with $f^B_k(\bar\tau) \le Q$; or
--   2. if there is no such B-job, an unscheduled A-job $J^A_h$ for which $f^A_h(\bar\tau)$ is minimum among the unscheduled A-jobs.
--
--   A **sketch run** is a list $\rho$ obtained from the empty list by legal steps. The sketch is nondeterministic (any such B-job, any minimizing A-job), and the relation describes every run.
--
--   **Formalization Note** `remSum p ρ` is $\bar\tau$; `IsSketchSuffix p fA fB Q ρ` is an inductive predicate with one constructor per kind of step, each requiring the fixed job not to be in `ρ` already.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, p. 232 ("Lawler's algorithm for this special case may be sketched as follows …")

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible

namespace TwoAgentSched

open Classical in
/-- `τ̄` for a partial schedule: the total processing time of the jobs **not** in `ρ` (the
unscheduled jobs). -/
noncomputable def remSum {nA nB : ℕ} (p : Job nA nB → ℝ) (ρ : List (Job nA nB)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ∉ ρ), p j

/-- **The §4 sketch of Lawler's algorithm** (p. 232), as a relation on partial runs: `ρ` is the
list of jobs fixed so far, in processing order (the last job of the schedule is the last entry,
and each step puts its job in front of `ρ`, i.e. last among the unscheduled jobs). With `τ̄` the
sum of the processing times of the unscheduled jobs, a step either
* fixes any unscheduled B-job `k` with `f^B_k(τ̄) ≤ Q` to end at `τ̄`, or
* when no unscheduled B-job has `f^B_k(τ̄) ≤ Q`, fixes an unscheduled A-job `h` whose
  `f^A_h(τ̄)` is minimum among the unscheduled A-jobs. -/
inductive IsSketchSuffix {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) : List (Job nA nB) → Prop
  | nil : IsSketchSuffix p fA fB Q []
  | stepB {ρ : List (Job nA nB)} (k : Fin nB) :
      IsSketchSuffix p fA fB Q ρ → Sum.inr k ∉ ρ → fB k (remSum p ρ) ≤ Q →
      IsSketchSuffix p fA fB Q (Sum.inr k :: ρ)
  | stepA {ρ : List (Job nA nB)} (h : Fin nA) :
      IsSketchSuffix p fA fB Q ρ → Sum.inl h ∉ ρ →
      (∀ k : Fin nB, Sum.inr k ∉ ρ → Q < fB k (remSum p ρ)) →
      (∀ h' : Fin nA, Sum.inl h' ∉ ρ → fA h (remSum p ρ) ≤ fA h' (remSum p ρ)) →
      IsSketchSuffix p fA fB Q (Sum.inl h :: ρ)

end TwoAgentSched


