-- Prove2me | Definitions.Def_TwoAgentSched_Feasible
-- name    : TwoAgentSched_Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:44:54.885995+00:00
-- url     : https://prove2.me/theorems/bc255fac-fdbf-4f22-a3a2-f4802875392d
-- title:
--   Jobs of two agents, feasible schedules, sequences and no-idle completion times
-- statement:
--   Two agents $A$ and $B$ share one machine. Agent $A$ owns the jobs $J^A_1,\dots,J^A_{n_A}$ and agent $B$ the jobs $J^B_1,\dots,J^B_{n_B}$; each job $j$ has a processing time $p_j$.
--
--   1. A **feasible schedule** is an assignment of starting times $S_j$ to the $n=n_A+n_B$ jobs such that all release dates are zero and jobs do not overlap on the machine:
--   $$
--   S_j \ge 0 \text{ for all } j, \qquad S_i + p_i \le S_j \ \text{ or } \ S_j + p_j \le S_i \quad (i \ne j).
--   $$
--   The completion time of job $j$ is $C_j = S_j + p_j$.
--   2. A **sequence** is an ordering $\sigma$ of all jobs, each job occurring exactly once.
--   3. The **no-idle completion time** of job $j$ in $\sigma$ is the total processing time of the jobs of $\sigma$ up to and including $j$:
--   $$
--   C_j(\sigma) = \sum_{i \preceq_\sigma j} p_i .
--   $$
--   It is the completion time when each job is started as soon as the previous job in the sequence is completed.
--
--   These are the objects of §3 on which every objective and constraint of the paper is evaluated.
--
--   **Formalization Note** The job type is `Fin nA ⊕ Fin nB`. `Feasible` and `IsSeq` are stated for an arbitrary job type (so that Lawler's single-agent problem can use them with `Fin n`); a sequence is a duplicate-free list containing every job, and `seqC p σ j` sums `p` over the prefix of `σ` ending with `j`. Zero-length jobs are allowed, and may share a start time with another job.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §3, p. 231 ("Let σ indicate a feasible schedule of the n = n_A + n_B jobs, i.e., a feasible assignment of starting times to the jobs of both agents"; zero release dates; nonpreemptive jobs on a common machine)

import Mathlib

namespace TwoAgentSched

/-- The jobs of the two agents: `Sum.inl h` is the A-job `J^A_h` (`h < n_A`) and `Sum.inr k` is
the B-job `J^B_k` (`k < n_B`). Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper. Res. 52(2)
(2004), §3, p. 231. -/
abbrev Job (nA nB : ℕ) : Type := Fin nA ⊕ Fin nB

/-- **Feasible schedule** (§3, p. 231: "a feasible assignment of starting times to the jobs"):
start times `S j` on one machine, zero release dates (`0 ≤ S j`), nonpreemptive and without
overlap (for two distinct jobs, one completes before the other starts). Completion times are
`S j + p j`. Zero-length jobs may share a start time. -/
def Feasible {ι : Type} (p : ι → ℝ) (S : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ S j) ∧ ∀ i j, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i

/-- A **sequence** (processing order) of all jobs: a duplicate-free list containing every job. -/
def IsSeq {ι : Type} (σ : List ι) : Prop :=
  σ.Nodup ∧ ∀ j, j ∈ σ

/-- The **no-idle completion time** of job `j` in the sequence `σ`: the sum of the processing
times of the prefix of `σ` ending with `j` (§3, p. 231: "each job is started as soon as the
previous job in the sequence is completed"). -/
def seqC {ι R : Type} [DecidableEq ι] [AddCommMonoid R] (p : ι → R) (σ : List ι) (j : ι) : R :=
  ((σ.take (σ.idxOf j + 1)).map p).sum

end TwoAgentSched


