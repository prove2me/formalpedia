-- Prove2me | Definitions.Def_MooreLateJobs_Shared_completionTime
-- name    : MooreLateJobs_Shared_completionTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:03:01.559647+00:00
-- url     : https://prove2.me/theorems/519e3be0-491b-4520-ac15-b0c219322304
-- title:
--   Schedules and completion times on a single machine
-- statement:
--   Let $J$ be a finite set of jobs; job $j$ has a known processing time $t_j$. A single machine starts at time $0$ and processes the jobs one after another, without idle time and without interrupting a job (Moore 1968, p. 102).
--
--   1. A **schedule** of $J$ is a specific ordering $S=(J_{i_1},\dots,J_{i_n})$ of the jobs of $J$, each job appearing exactly once (p. 104).
--   2. In a sequence $S=(J_{i_1},\dots,J_{i_n})$, the job in position $k$ completes at
--   $$
--   C_{i_k}=\sum_{m=1}^{k} t_{i_m}
--   $$
--   ($C_i$ is named on p. 105 as "the completion time of job $J_i$ in the schedule $S$"; the sum is what the p. 102 model gives: the machine starts at $t=0$, due-dates are defined relative to $t=0$, and it runs continuously without interruption).
--
--   These are the basic objects of every single-machine sequencing problem in the paper. This one definition serves both chunks of the series: `01-number-late` (pp. 102, 104–105: the late set $L=\{J_i: C_i>D_i\}$ and the number of late jobs are built on it) and `02-max-deferral` (pp. 102, 104–105, 108: the deferral cost $P_j(C_j)$ and the "no late jobs at level $y$" condition are evaluated at $C_j$).
--
--   **Formalization Note** A schedule is a duplicate-free list whose elements are exactly the elements of $J$. Positions are 0-based: `completionAt t l k` is the sum of the processing times of the first $k+1$ entries, and `completionTime t l j` evaluates it at the position of $j$ (its first occurrence).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 102 (the model, Introduction), p. 104 (Definition of a schedule) and p. 105 (C_i, the completion time of job J_i in the schedule S); used by chunks 01-number-late (pp. 102, 104-105) and 02-max-deferral (pp. 102, 104-105, 108)

import Mathlib

namespace MooreLateJobs.Shared

/-- A schedule of the job set `J` (Moore 1968, p. 104): a specific ordering of the jobs of `J`,
encoded as a duplicate-free list whose elements are exactly the jobs of `J`. -/
def IsSchedule {ι : Type*} (J : Finset ι) (l : List ι) : Prop :=
  l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ J

/-- Completion time of the job in (0-based) position `k` of the sequence `l`: the machine starts
at time `0` and processes the jobs one after another without idle time or interruption (p. 102),
so the `k`-th job completes at the sum of the processing times of the first `k + 1` jobs. -/
def completionAt {ι : Type*} (t : ι → ℝ) (l : List ι) (k : ℕ) : ℝ :=
  ((l.take (k + 1)).map t).sum

/-- Completion time `C_j` of job `j` in the sequence `l` (the completion time at the position of
its first occurrence; sequences in this development are duplicate-free). -/
def completionTime {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (l : List ι) (j : ι) : ℝ :=
  completionAt t l (l.idxOf j)

end MooreLateJobs.Shared


