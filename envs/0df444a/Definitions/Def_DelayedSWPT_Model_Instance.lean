-- Prove2me | Definitions.Def_DelayedSWPT_Model_Instance
-- name    : DelayedSWPT_Model_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:07:43.215441+00:00
-- url     : https://prove2.me/theorems/f303c865-3734-4193-ae31-1d5c442b84c5
-- title:
--   Single-machine instances with release dates, nonpreemptive schedules and total weighted completion time
-- statement:
--   An **instance** of the single-machine problem consists of $n$ jobs. Job $j$ has an integer release date $r_j \ge 0$, an integer processing time $p_j \ge 1$ and a positive real weight $w_j > 0$.
--
--   A **schedule** of a finite set of jobs is given by integer start times $S_j$; job $j$ completes at $C_j = S_j + p_j$ and occupies the interval $[S_j, S_j + p_j)$. The schedule is **feasible** when
--
--   $$S_j \ge r_j \quad\text{for every } j, \qquad\text{and}\qquad S_i + p_i \le S_j \ \text{ or } \ S_j + p_j \le S_i \quad\text{for all } i \ne j,$$
--
--   that is, no job starts before its release date and no two jobs are processed at the same time (preemption is not allowed, idle time is). Its **total weighted completion time** is
--
--   $$C(S) = \sum_{j} w_j C_j = \sum_j w_j (S_j + p_j).$$
--
--   A schedule is **optimal** when it is feasible and no feasible schedule has a smaller total weighted completion time.
--
--   These notions are the offline problem $1\,|\,r_j\,|\,\sum w_j C_j$ against which the online algorithm Delayed SWPT is measured. Feasibility, cost and optimality are stated for an arbitrary finite job type, so that the extended problem (E), whose jobs are the original jobs plus unit gap jobs, uses the same notions.
--
--   **Formalization Note** Jobs of an instance are indexed by `Fin n` (0-based). Times are natural numbers, as in the paper's standing assumption that all release dates and processing times are integers (p. 688). The hypotheses $p_j \ge 1$ and $w_j > 0$ are part of the instance.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 686, §1 (problem statement); p. 688, §2 (integer data, schedules by start times)

import Mathlib

namespace DelayedSWPT.Model

/-- An instance of the single-machine problem of Anderson and Potts (2004), §1, p. 686, with
the integer data of §2, p. 688: `n` jobs, job `j` has release date `r j`, processing time
`p j ≥ 1` and positive weight `w j`. Jobs are indexed by `Fin n` (0-based). -/
structure Instance (n : ℕ) where
  r : Fin n → ℕ
  p : Fin n → ℕ
  w : Fin n → ℝ
  p_pos : ∀ j, 1 ≤ p j
  w_pos : ∀ j, 0 < w j

/-- A nonpreemptive single-machine schedule, given by integer start times `S j`, is feasible
when no job starts before its release date and no two jobs overlap: job `j` occupies
`[S j, S j + p j)`. Idle time is allowed. The job type `ι` is any finite type, so that the
extended problem (E), whose jobs are the original jobs plus gap jobs, uses the same notion. -/
def IsFeasible {ι : Type*} (r p : ι → ℕ) (S : ι → ℕ) : Prop :=
  (∀ j, r j ≤ S j) ∧ ∀ i j, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i

/-- Total weighted completion time `∑ⱼ wⱼ Cⱼ` with `Cⱼ = S j + p j`. -/
noncomputable def cost {ι : Type*} [Fintype ι] (w : ι → ℝ) (p S : ι → ℕ) : ℝ :=
  ∑ j, w j * ((S j + p j : ℕ) : ℝ)

/-- `S` is an optimal (offline) schedule: feasible, and no feasible schedule has smaller
total weighted completion time. -/
def IsOptimal {ι : Type*} [Fintype ι] (r p : ι → ℕ) (w : ι → ℝ) (S : ι → ℕ) : Prop :=
  IsFeasible r p S ∧ ∀ S' : ι → ℕ, IsFeasible r p S' → cost w p S ≤ cost w p S'

end DelayedSWPT.Model


