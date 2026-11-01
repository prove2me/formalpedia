-- Prove2me | Definitions.Def_SerialBatchTardy_Model
-- name    : SerialBatchTardy_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:08.391094+00:00
-- url     : https://prove2.me/theorems/e68b4ce1-63d8-4f78-80e4-44cf0e8b5dfd
-- title:
--   Serial batch scheduling with release dates: schedules, feasibility, weighted tardy jobs
-- statement:
--   An instance of $1|\text{s-batch}(\infty),r_j|\sum w_jU_j$ consists of a setup time $\Delta\in\mathbb N$ and a list of $n$ jobs; job $j$ has a processing time $p_j\in\mathbb N$, a weight $w_j\in\mathbb N$, a release date $r_j\in\mathbb Z$ and a due date $d_j\in\mathbb Z$.
--
--   A **schedule** partitions the jobs into batches and gives each batch $B$ a start time $S_B\in\mathbb Z$. The processing time of a batch is $p_B=\Delta+\sum_{j\in B}p_j$, and every job of $B$ completes at
--
--   $$C_j=C_B=S_B+p_B.$$
--
--   The schedule is **feasible** if $S_B\ge r_j$ for every job $j\in B$ and, for any two distinct batches $B,B'$, one completes before the other starts: $C_B\le S_{B'}$ or $C_{B'}\le S_B$. Job $j$ is **tardy** if $C_j>d_j$ ($U_j=1$), and early otherwise. The objective is the **weighted number of tardy jobs** $\sum_j w_jU_j$; a schedule is **optimal** if it is feasible and no feasible schedule has a smaller objective. The parameters $\#p,\#w,\#d,\#r$ are the numbers of distinct processing times, weights, due dates and release dates.
--
--   **Formalization Note** A batch is a label $b\in\mathbb N$ carried by its jobs; only labels in use matter. The non-overlap condition agrees with the paper's "$S_{B'}\notin[S_B,C_B)$" for batches of positive length. The release-date condition applies to tardy jobs as well. Positivity of the weights is imposed by the problem languages, not here.
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), §2, p.548 (PDF p.4), and §1.2, p.546 (PDF p.2), definition of 1|s-batch(∞)|∑w_jU_j and of #p, #w, #d

import Mathlib

set_option autoImplicit false

namespace SerialBatchTardy

/-- A **job** of `1|s-batch(∞), r_j|∑ w_jU_j`: processing time `p`, weight `w`, release date `r`
and due date `d`. Hermelin, Mnich & Omlor, *Serial batching to minimize the weighted number of
tardy jobs*, J. Scheduling 27 (2024), §2, p.548 (PDF p.4): "a set J of n jobs each of which is
characterized by an integer due date d_j, integer processing time p_j, and integer release date
r_j and a positive integer weight w_j".

**Formalization Note.** `p, w ∈ ℕ` and `r, d ∈ ℤ`. Positivity of the weights is imposed where the
problem is posed (the languages of `Def_SerialBatchTardy_Encoding`), not in this structure. -/
structure Job where
  p : ℕ
  w : ℕ
  r : ℤ
  d : ℤ
  deriving DecidableEq, Repr

/-- An **instance**: the batch setup time `Δ` (`setup`) and the job list (jobs are listed one by
one; job `j` is `jobs[j]`, indices from `0`). -/
structure Instance where
  setup : ℕ
  jobs : List Job
  deriving DecidableEq, Repr

/-- Job `j` of an instance. -/
def Instance.job (I : Instance) (j : Fin I.jobs.length) : Job := I.jobs.get j

/-- A **schedule**: a partition of the jobs into batches, given by the batch label `batch j ∈ ℕ`
of each job, and a start time `start b ∈ ℤ` for each batch label `b` (only labels in use matter).
p.548: "a partition the job set J into a set B of batches, and then assign a starting time S_B to
each batch B". -/
structure Schedule (I : Instance) where
  batch : Fin I.jobs.length → ℕ
  start : ℕ → ℤ

variable {I : Instance}

/-- Batch label `b` is used: some job is in it. -/
def Schedule.Used (σ : Schedule I) (b : ℕ) : Prop := ∃ j, σ.batch j = b

/-- The jobs of batch `b`. -/
def Schedule.batchJobs (σ : Schedule I) (b : ℕ) : Finset (Fin I.jobs.length) :=
  Finset.univ.filter fun j => σ.batch j = b

/-- The **processing time of a batch**, `p_B = Δ + ∑_{j ∈ B} p_j` (p.548). -/
def Schedule.batchLen (σ : Schedule I) (b : ℕ) : ℤ :=
  (I.setup : ℤ) + ∑ j ∈ σ.batchJobs b, ((I.job j).p : ℤ)

/-- The **completion time of a batch**, `C_B = S_B + p_B`; every job of `B` completes at `C_B`
(p.548: "C_j = S_B + p_B"). -/
def Schedule.comp (σ : Schedule I) (b : ℕ) : ℤ := σ.start b + σ.batchLen b

/-- **Feasibility**: every job starts no earlier than its release date (p.548: "a starting time
S_j ≥ r_j", with `S_j = S_B`), and no two distinct used batches are processed at the same time:
one of them completes before the other starts.

**Formalization Note.** The non-overlap condition is "`C_B ≤ S_{B'}` or `C_{B'} ≤ S_B`". For batches
of positive length it is the paper's "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546); the two
differ only for a batch of length zero (setup `0` and processing times `0`) starting exactly when
another batch starts. The release-date condition binds tardy jobs too. -/
def Schedule.Feasible (σ : Schedule I) : Prop :=
  (∀ j, (I.job j).r ≤ σ.start (σ.batch j)) ∧
  ∀ b b', σ.Used b → σ.Used b' → b ≠ b' → σ.comp b ≤ σ.start b' ∨ σ.comp b' ≤ σ.start b

/-- Job `j` is **tardy**: its completion time exceeds its due date, `C_j > d_j` (p.548: "U_j = 1 if
C_j > d_j"). A job with `C_j = d_j` is early. -/
def Schedule.IsTardy (σ : Schedule I) (j : Fin I.jobs.length) : Prop :=
  (I.job j).d < σ.comp (σ.batch j)

instance (σ : Schedule I) (j : Fin I.jobs.length) : Decidable (σ.IsTardy j) := by
  unfold Schedule.IsTardy; infer_instance

/-- The **weighted number of tardy jobs**, `∑_j w_j U_j` (p.548). -/
def Schedule.tardyWeight (σ : Schedule I) : ℕ :=
  ∑ j, if σ.IsTardy j then (I.job j).w else 0

/-- An **optimal schedule**: feasible, and of least weighted number of tardy jobs among all
feasible schedules (p.548: "find a schedule which minimizes the weighted number"). -/
def Schedule.IsOptimal (σ : Schedule I) : Prop :=
  σ.Feasible ∧ ∀ σ' : Schedule I, σ'.Feasible → σ.tardyWeight ≤ σ'.tardyWeight

/-- `#p`: the number of distinct processing times (p.546). -/
def numP (I : Instance) : ℕ := (I.jobs.map Job.p).toFinset.card

/-- `#w`: the number of distinct weights (p.546). -/
def numW (I : Instance) : ℕ := (I.jobs.map Job.w).toFinset.card

/-- `#d`: the number of distinct due dates (p.546). -/
def numD (I : Instance) : ℕ := (I.jobs.map Job.d).toFinset.card

/-- `#r`: the number of distinct release dates (p.547, p.553). -/
def numR (I : Instance) : ℕ := (I.jobs.map Job.r).toFinset.card

end SerialBatchTardy


