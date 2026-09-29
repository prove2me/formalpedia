-- Prove2me | Definitions.Def_MooreLateJobs_NumLate_lateSet
-- name    : MooreLateJobs_NumLate_lateSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:03:40.630306+00:00
-- url     : https://prove2.me/theorems/0d554db3-7f70-4c17-943e-cff76538d8be
-- title:
--   Schedules, completion times and the set L of late jobs
-- statement:
--   Let $J$ be a finite set of jobs; job $j$ has a processing time $t_j$ and a due-date $D_j$ (real numbers). A single machine starts at time $0$ and processes the jobs one after another, without idle time and without interrupting a job.
--
--   1. A **schedule** of $J$ is a specific ordering $(J_{i_1},\dots,J_{i_n})$ of the jobs of $J$, each job appearing exactly once.
--   2. In a sequence $S=(J_{i_1},\dots,J_{i_n})$, the job in position $k$ completes at
--   $$
--   C_{i_k}=\sum_{m=1}^{k} t_{i_m}.
--   $$
--   3. The **late set** of $S$ is $L=\{J_i : C_i>D_i\}$; its complement among the jobs of $S$ is the **early set** $E=\{J_i : C_i\le D_i\}$.
--
--   These are the basic objects of the single-machine problem of minimizing the number of late jobs, $|L|$.
--
--   **Formalization Note** Schedules (1) and completion times (2) are the group's shared definition `MooreLateJobs.Shared.completionTime` (`Shared.IsSchedule`, `Shared.completionAt`, `Shared.completionTime`): a schedule is a duplicate-free list whose elements are exactly the elements of $J$; positions are 0-based, `completionAt t l k` is the sum of the processing times of the first $k+1$ entries, and `completionTime t l j` evaluates it at the position of $j$ (its first occurrence). This item defines the late set (3). Lateness is strict ($C_j>D_j$), as in the paper.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 102 (the model) and pp. 104-105 (Definition of a schedule; the sets E and L)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace MooreLateJobs.NumLate

/-- The set `L` of late jobs of the sequence `l` (p. 105): `J_j ∈ L` iff `C_j > D_j`.
The early set `E` (`C_j ≤ D_j`) is the complement of `L` among the jobs of `l`. -/
noncomputable def lateSet {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (l : List ι) : Finset ι :=
  l.toFinset.filter (fun j => D j < Shared.completionTime t l j)

end MooreLateJobs.NumLate


