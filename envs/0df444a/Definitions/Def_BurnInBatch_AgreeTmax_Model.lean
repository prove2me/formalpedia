-- Prove2me | Definitions.Def_BurnInBatch_AgreeTmax_Model
-- name    : BurnInBatch_AgreeTmax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:39.279518+00:00
-- url     : https://prove2.me/theorems/4c6620d7-7cc9-47fd-9441-bc3b42cc3bbc
-- title:
--   §2 and §3: the batch processing machine without release times, batch schedules, makespan, $T_{\max}$, batch-EDD order and agreeable data
-- statement:
--   This file fixes the single **batch processing machine** of Lee, Uzsoy and Martin-Vega in the setting of their §3 problem $1/B/T_{\max}$, in which all jobs are available at time $0$.
--
--   There are $n$ jobs $1,\dots,n$. Job $i$ has a processing time $p_i\in\mathbb N$ and a due date $d_i\in\mathbb N$. The machine processes up to $B$ jobs simultaneously; the jobs of a **batch** are processed together, and the batch takes the processing time of its longest job,
--   $$t(P)=\max_{i\in P}p_i .$$
--   A **batch schedule** of a set $J$ of jobs is a sequence $S=(P_1,\dots,P_m)$ of batches in processing order such that
--
--   1. every batch is nonempty and contains at most $B$ jobs, all from $J$;
--   2. the batches are pairwise disjoint, and every job of $J$ lies in some batch.
--
--   Batches run back to back from time $0$: batch $P_k$ completes at $C(P_k)=t(P_1)+\dots+t(P_k)$, and every job of $P_k$ completes at $C(P_k)$. The **makespan** is $C_{\max}(S)=t(P_1)+\dots+t(P_m)$ ($0$ for the empty schedule), and the **maximum tardiness** is
--   $$T_{\max}(S)=\max_{k}\ \max_{i\in P_k}\ \max\{0,\ C(P_k)-d_i\}$$
--   ($0$ for the empty schedule). A schedule with $T_{\max}=0$ completes every job by its due date; the paper calls it feasible.
--
--   The file also defines: the set $\{1,\dots,j\}$ of the first $j$ jobs; **batch-EDD order** (Definition 1): for any two batches $P$, $Q$ with $P$ processed before $Q$, there is no pair $i\in P$, $j\in Q$ with $d_i>d_j$; **agreeable** processing times and due dates: $p_i<p_j$ implies $d_i\le d_j$; and **consecutive** schedules: every batch is a set of consecutively indexed jobs and the batches appear in increasing order of index (a consecutive partition).
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Jobs are `Fin n`, so the paper's job $i$ is index $i-1$, and $\{1,\dots,j\}$ is `jobsUpTo n j`, the indices below $j$. Data are natural numbers (the paper assumes integral data, p. 769). The batch time is `Finset.sup`, which is the maximum on the nonempty batches of a valid schedule. $\max\{0,\cdot\}$ is truncated subtraction in $\mathbb N$. Batches start as early as possible (no inserted idle time), which is the paper's convention and cannot help a regular objective. The paper prints agreeable as "$p_i\le p_j$ implies $d_i\le d_j$", which forces equal due dates for equal processing times; the strict form used here is weaker as a hypothesis, so statements assuming it imply the printed ones. Batch positions are `Fin S.length`.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 766, §2, Assumptions 1–3; p. 767, Definition 1; p. 768, justification of Algorithm DP1 (consecutive partition); p. 769, §3 (1/B/T_max, agreeable processing times and due dates)

import Mathlib

namespace BurnInBatch.AgreeTmax

/-! The single batch processing machine of Lee, Uzsoy & Martin-Vega, *Efficient Algorithms for
Scheduling Semiconductor Burn-In Operations*, Oper. Res. 40(4) (1992), §2 (p. 766), Definition 1
(p. 767), specialised to §3's problem `1/B/T_max` in which all jobs are available at time 0
(p. 769).

Jobs are `Fin n` (the paper's job `i` is `i - 1`). Each job `i` has a processing time `p i` and a
due date `d i` (natural numbers: the paper assumes all data integral, p. 769). A batch schedule is
a list of batches (finite sets of jobs) in processing order. A batch takes the processing time of
its longest job; batches are processed back to back from time 0 (no inserted idle time, which
cannot help any regular objective; with no release times this is the paper's convention). -/

/-- The jobs `1, …, j` of the paper, i.e. the jobs with 0-based index `< j`. -/
def jobsUpTo (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < j

/-- A valid batch schedule of the job set `J` on a machine of capacity `B` (Assumption 2):
every batch is nonempty, has at most `B` jobs and consists of jobs of `J`; the batches are
pairwise disjoint; every job of `J` lies in some batch. -/
def IsValid {n : ℕ} (B : ℕ) (J : Finset (Fin n)) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty) ∧ (∀ P ∈ S, P.card ≤ B) ∧ (∀ P ∈ S, P ⊆ J) ∧
    S.Pairwise Disjoint ∧ ∀ i ∈ J, ∃ P ∈ S, i ∈ P

/-- Processing time of a batch: the processing time of its longest job (Assumption 3). -/
def batchTime {n : ℕ} (p : Fin n → ℕ) (P : Finset (Fin n)) : ℕ :=
  P.sup p

/-- Completion time of the batch at position `k` (0-based) of `S`: the batches `0, …, k` run back
to back from time 0. -/
def batchCompletion {n : ℕ} (p : Fin n → ℕ) (S : List (Finset (Fin n))) (k : ℕ) : ℕ :=
  ((S.take (k + 1)).map (batchTime p)).sum

/-- Makespan `C_max`: completion time of the last batch (0 for the empty schedule). -/
def makespan {n : ℕ} (p : Fin n → ℕ) (S : List (Finset (Fin n))) : ℕ :=
  (S.map (batchTime p)).sum

/-- Maximum tardiness `T_max = max_i max(0, C_i - d_i)`, where a job's completion time `C_i` is
the completion time of its batch (truncated subtraction in `ℕ` is `max(0, ·)`); `0` for the empty
schedule. -/
def Tmax {n : ℕ} (p d : Fin n → ℕ) (S : List (Finset (Fin n))) : ℕ :=
  Finset.univ.sup fun k : Fin S.length => (S.get k).sup fun i => batchCompletion p S k.val - d i

/-- Definition 1 (p. 767): the sequence is in batch-EDD order if for any two batches `P`, `Q`
with `P` processed before `Q` there is no pair of jobs `i ∈ P`, `j ∈ Q` with `d i > d j`. -/
def IsBatchEDD {n : ℕ} (d : Fin n → ℕ) (S : List (Finset (Fin n))) : Prop :=
  ∀ a b : Fin S.length, a < b → ∀ i ∈ S.get a, ∀ j ∈ S.get b, ¬ d j < d i

/-- Processing times and due dates are agreeable (p. 769), in the strict form:
`p i < p j` implies `d i ≤ d j`. -/
def Agreeable {n : ℕ} (p d : Fin n → ℕ) : Prop :=
  ∀ i j : Fin n, p i < p j → d i ≤ d j

/-- The batches are sets of consecutively indexed jobs, and the batches appear in increasing
order of job index: a consecutive partition (p. 768). -/
def IsConsecutive {n : ℕ} (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, ∀ i j k : Fin n, i ∈ P → k ∈ P → i ≤ j → j ≤ k → j ∈ P) ∧
    ∀ a b : Fin S.length, a < b → ∀ i ∈ S.get a, ∀ j ∈ S.get b, i < j

end BurnInBatch.AgreeTmax


