-- Prove2me | Definitions.Def_BurnInBatch_ReleaseTmax_Model
-- name    : BurnInBatch_ReleaseTmax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:35.5643+00:00
-- url     : https://prove2.me/theorems/3dfdb026-276c-4e27-bf0c-ad0ef702b2af
-- title:
--   §2 and §3: one batch machine with release times and equal processing times — batch schedules, completion times, makespan, $T_{\max}$, batch-EDD order
-- statement:
--   This module fixes the scheduling model of §2–§3 for the problem $1/r_i, p_i = p, B/T_{\max}$: one **batch processing machine** that processes up to $B$ jobs simultaneously, and $n$ jobs, where job $i$ has a release time $r_i$, a due date $d_i$, and the common processing time $p$ (all natural numbers).
--
--   1. **Batch schedule.** A batch schedule of a set $J$ of jobs is a finite sequence of batches $P_1, P_2, \dots, P_m$ in processing order: each batch is a nonempty set of at most $B$ jobs, the batches are pairwise disjoint, and their union is exactly $J$.
--   2. **Completion times.** A batch cannot start before all its jobs are released, nor before the previous batch is completed; it starts as early as these two conditions allow and takes time $p$. With $r(P) = \max\{r_k \mid k \in P\}$ and $C(P_0) = 0$,
--   $$
--   C(P_k) = \max\{r(P_k),\, C(P_{k-1})\} + p, \qquad k = 1, \dots, m.
--   $$
--   The completion time $C_j$ of a job $j$ is the completion time of the batch containing it, and the **makespan** is $C(P_m)$ ($0$ for the empty schedule).
--   3. **Feasibility and tardiness.** A schedule is **on time** (has $T_{\max} = 0$) for $J$ if $C_j \le d_j$ for every $j \in J$. The **maximum tardiness** is $T_{\max} = \max_{j \in J} \max\{0, C_j - d_j\}$.
--   4. **Definition 1 (batch-EDD).** A sequence is in batch-EDD order if for any two batches $P$ and $Q$, $P$ processed before $Q$, there is no pair $i \in P$, $j \in Q$ with $d_i > d_j$.
--   5. **Consecutive batches.** A schedule has consecutive batches if every batch is a set of consecutively indexed jobs $\{a, a+1, \dots, b-1\}$ and every job of an earlier batch has a smaller index than every job of a later batch.
--   6. **Prefixes.** For $0 \le j \le n$, "jobs $1, \dots, j$" is the set of the first $j$ jobs of the index order.
--
--   These are the objects in terms of which Lemma 1, Lemma 2 and the correctness of Algorithm DP1 are stated.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based: the paper's job $i$ is `i - 1`, and the prefix "jobs $1,\dots,j$" is `prefixJobs n j`, the jobs of index `< j`. Schedules are semi-active (every batch starts as early as possible); inserted idle time never helps a regular objective and the paper never uses it. `batchRelease` is `Finset.sup`, which equals the maximum for the nonempty batches of a schedule. `jobCompletion` returns the completion of the first batch containing the job (the batches are disjoint) and $0$ for a job in no batch; it is only used for jobs of $J$. In `tmax`, natural-number subtraction truncates at $0$, so `C_j - d_j` is $\max\{0, C_j - d_j\}$, and the maximum over an empty $J$ is $0$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 766, §2 Assumptions 1–3; p. 767, Definition 1 and proof of Lemma 1 (C(P) = max{r(P), C(P − 1)} + p); p. 768, justification of DP1

import Mathlib

namespace BurnInBatch.ReleaseTmax

/-- The first `j` jobs of the index order: the 0-based jobs `0, …, j - 1`, i.e. the paper's
jobs `1, …, j`. -/
def prefixJobs (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val < j)

/-- A batch schedule of the job set `J` on one batch machine of capacity `B`: a list of batches
in processing order, each nonempty with at most `B` jobs, pairwise disjoint, whose union is `J`. -/
def IsBatchSchedule {n : ℕ} (B : ℕ) (J : Finset (Fin n)) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty ∧ P.card ≤ B) ∧
  S.Pairwise (fun P Q => Disjoint P Q) ∧
  ∀ j : Fin n, j ∈ J ↔ ∃ P ∈ S, j ∈ P

/-- The release time `r(P) = max {r_k | k ∈ P}` of a batch (for a nonempty batch). -/
def batchRelease {n : ℕ} (r : Fin n → ℕ) (P : Finset (Fin n)) : ℕ :=
  P.sup r

/-- Completion time of the last batch when the batches `S` are processed in order, each of
duration `p`, the previous batch having completed at time `t`: a batch starts at
`max (previous completion, r(P))` and completes `p` later. -/
def finish {n : ℕ} (p : ℕ) (r : Fin n → ℕ) : List (Finset (Fin n)) → ℕ → ℕ
  | [], t => t
  | P :: S, t => finish p r S (max t (batchRelease r P) + p)

/-- The makespan of the batch schedule `S`: the completion time of its last batch, starting from
time `0` (it is `0` for the empty schedule). -/
def makespan {n : ℕ} (p : ℕ) (r : Fin n → ℕ) (S : List (Finset (Fin n))) : ℕ :=
  finish p r S 0

/-- Auxiliary recursion for `jobCompletion`: `t` is the completion time of the previous batch. -/
def jobCompletionAux {n : ℕ} (p : ℕ) (r : Fin n → ℕ) (j : Fin n) :
    List (Finset (Fin n)) → ℕ → ℕ
  | [], _ => 0
  | P :: S, t =>
      if j ∈ P then max t (batchRelease r P) + p
      else jobCompletionAux p r j S (max t (batchRelease r P) + p)

/-- The completion time `C_j` of job `j` in the batch schedule `S`: the completion time of the
batch containing `j` (only used for jobs that lie in some batch). -/
def jobCompletion {n : ℕ} (p : ℕ) (r : Fin n → ℕ) (S : List (Finset (Fin n))) (j : Fin n) : ℕ :=
  jobCompletionAux p r j S 0

/-- Every job of `J` is on time in `S`: `C_j ≤ d_j`. For a batch schedule of `J` this is the
paper's "schedule with `T_max = 0`" (a feasible schedule). -/
def AllOnTime {n : ℕ} (p : ℕ) (r d : Fin n → ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) : Prop :=
  ∀ j ∈ J, jobCompletion p r S j ≤ d j

/-- Maximum tardiness `T_max = max_{j ∈ J} max(0, C_j − d_j)` of `S` over the jobs of `J`
(natural-number subtraction truncates at `0`, so `C_j - d_j` is `max(0, C_j − d_j)`; the
maximum over an empty `J` is `0`). -/
def tmax {n : ℕ} (p : ℕ) (r d : Fin n → ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) : ℕ :=
  J.sup (fun j => jobCompletion p r S j - d j)

/-- Definition 1 (batch-EDD order): for any two batches `P` before `Q` in `S` there are no jobs
`i ∈ P`, `j ∈ Q` with `d_i > d_j`. -/
def IsBatchEDD {n : ℕ} (d : Fin n → ℕ) (S : List (Finset (Fin n))) : Prop :=
  S.Pairwise (fun P Q => ∀ i ∈ P, ∀ j ∈ Q, d i ≤ d j)

/-- Every batch of `S` is a set of consecutively indexed jobs `{a, a + 1, …, b - 1}` (0-based),
and the batches appear in increasing index order: every job of an earlier batch has a smaller
index than every job of a later batch. -/
def IsConsecutive {n : ℕ} (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, ∃ a b : ℕ, P = Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b)) ∧
  S.Pairwise (fun P Q => ∀ i ∈ P, ∀ j ∈ Q, i < j)

end BurnInBatch.ReleaseTmax


