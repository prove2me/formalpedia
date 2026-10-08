-- Prove2me | Definitions.Def_SchedComplexity_Partition_TwoMachineModel
-- name    : SchedComplexity_Partition_TwoMachineModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:46:49.744974+00:00
-- url     : https://prove2.me/theorems/9f55ca3e-c246-41ef-b3d0-d2335248dd8d
-- title:
--   Nonpreemptive schedules of single-operation jobs on two identical machines, $C_j$, and $\sum w_jC_j$
-- statement:
--   The model of Section 3 of Brucker, Lenstra & Rinnooy Kan for a parallel shop ($\ell = I$) with $m = 2$ identical machines $M_1, M_2$. There are $n$ jobs $J_1,\dots,J_n$; each consists of a single operation with a processing time $p_j \in \mathbb N$ and has a weight $w_j\in\mathbb N$; all jobs are available at time $0$.
--
--   1. A **schedule** assigns to each job $J_j$ a machine and a starting time $B_j\in\mathbb N$. Its **completion time** is $C_j = B_j + p_j$.
--   2. A schedule is **feasible** if two distinct jobs on the same machine never overlap: job $J_j$ occupies its machine during $[B_j, B_j+p_j)$, and these half-open intervals are pairwise disjoint on each machine. A job with $p_j=0$ occupies the empty interval. Idle time is allowed.
--   3. A feasible schedule is **non-idle** if each machine processes its jobs without idle time from time $0$: every job on a machine completes by the total processing time of the jobs assigned to that machine.
--   4. The total weighted completion time is $\sum_{j=1}^n w_j C_j$.
--
--   These are the objects in which both target problems $n|2|I|C_{\max}$ and $n|2|I|\sum w_jC_j$ of Theorem 3 are stated.
--
--   **Formalization Note** Jobs are `Fin n` and machines `Fin 2` (machine `0` is $M_1$). Starting times are natural numbers: Section 3 computes $B_j$ and $C_j$ from processing orders on nonnegative integer data, so they are integers; since both criteria are regular, real starting times would give the same yes-instances. Processing times may be $0$ (p. 6: all data are nonnegative integers).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 6–7, Section 3 (ℓ = I, criteria C_max and Σw_jC_j)

import Mathlib

namespace SchedComplexity.Partition

/-- A nonpreemptive schedule of `n` single-operation jobs `J_j`, `j < n`, on two identical
machines (Brucker, Lenstra & Rinnooy Kan 1975, Section 3, pp. 6–7, `ℓ = I`, `m = 2`): job `j` is
processed on machine `machine j` (machine `0` is the paper's `M_1`, machine `1` is `M_2`) from
its starting time `start j = B_j`, a natural number. -/
structure Schedule (n : ℕ) where
  machine : Fin n → Fin 2
  start : Fin n → ℕ

namespace Schedule

variable {n : ℕ}

/-- The completion time `C_j = B_j + p_j` of job `j` under processing times `p`. -/
def completion (p : Fin n → ℕ) (σ : Schedule n) (j : Fin n) : ℕ :=
  σ.start j + p j

/-- Feasibility: job `j` occupies its machine during the half-open interval `[B_j, B_j + p_j)`,
and two distinct jobs assigned to the same machine occupy disjoint intervals ("each machine can
handle at most one job at a time", p. 6). Two such intervals meet iff both are nonempty
(`0 < p_j`, `0 < p_k`) and each starts before the other ends; a job of processing time `0`
occupies the empty interval and conflicts with nothing. Idle time is allowed. -/
def IsFeasible (p : Fin n → ℕ) (σ : Schedule n) : Prop :=
  ∀ j k : Fin n, j ≠ k → σ.machine j = σ.machine k →
    ¬ (0 < p j ∧ 0 < p k ∧ σ.start j < σ.start k + p k ∧ σ.start k < σ.start j + p j)

/-- A feasible schedule in which each machine processes its jobs without idle time from time
`0`: every job assigned to a machine completes by the total processing time of the jobs on that
machine (together with feasibility, the jobs of each machine then fill `[0, Σ p)` exactly). -/
def IsNonIdle (p : Fin n → ℕ) (σ : Schedule n) : Prop :=
  σ.IsFeasible p ∧
    ∀ j : Fin n, σ.completion p j ≤
      ∑ k ∈ Finset.univ.filter (fun k => σ.machine k = σ.machine j), p k

/-- The total weighted completion time `Σ_j w_j C_j` (p. 7). -/
def sumWC (p w : Fin n → ℕ) (σ : Schedule n) : ℕ :=
  ∑ j : Fin n, w j * σ.completion p j

end Schedule

end SchedComplexity.Partition


