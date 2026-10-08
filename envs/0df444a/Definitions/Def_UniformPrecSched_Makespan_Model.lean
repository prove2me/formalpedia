-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Model
-- name    : UniformPrecSched_Makespan_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:45:26.921585+00:00
-- url     : https://prove2.me/theorems/900e4ef1-a21a-4b3c-b0d9-1b5e904c48c3
-- title:
--   Q|prec|C_max: instances, nonpreemptive schedules, speed classes, loads D_k, chain bound C, speed-based list schedules
-- statement:
--   This file fixes the model of Chudak and Shmoys for scheduling precedence-constrained jobs on uniformly related parallel machines, $Q|prec|C_{\max}$.
--
--   1. **Instance.** There are $n$ jobs and $m \ge 1$ machines. Job $j$ requires $p_j > 0$ units of processing; machine $i$ runs at speed $s_i > 0$, so job $j$ takes $p_j/s_i$ time units on machine $i$. A strict partial order $\prec$ on the jobs gives the precedence constraints: $j \prec k$ means that job $k$ may not start until job $j$ has been completed.
--   2. **Schedule.** A feasible schedule processes each job $j$ without interruption on one machine $\mu(j)$, from its start time $S_j \ge 0$ to its completion time $C_j = S_j + p_j/s_{\mu(j)}$. Each machine processes at most one job at a time, and $j \prec k$ implies $C_j \le S_k$.
--   3. **Length.** The length of a schedule is $C_{\max} = \max_j C_j$ (and $0$ if there are no jobs).
--   4. **Speed classes.** Let $K$ be the number of distinct machine speeds and $\bar s_1 > \bar s_2 > \cdots > \bar s_K$ those speeds; $m_k \ge 1$ is the number of machines of speed $\bar s_k$.
--   5. **Assignment, loads, chains.** A job assignment gives each job $j$ the index $k(j)$ of the speed at which it is to be processed. Its loads are
--   $$D_k = \frac{1}{m_k}\sum_{j : k(j) = k} \frac{p_j}{\bar s_k}, \qquad k = 1,\dots,K,$$
--   and $C$ is the maximum over all chains $\mathcal C$ (sets of jobs that are pairwise comparable under $\prec$, the empty chain included) of $\sum_{j \in \mathcal C} p_j/\bar s_{k(j)}$.
--   6. **Speed-based list schedules.** The speed-based list scheduling algorithm builds the schedule in time: whenever a job completes, each idle machine of speed $\bar s_k$ takes the first job $j$ on the list with $k(j) = k$ whose predecessors have all been completed. A schedule is called a speed-based list schedule for the assignment $k$ when (a) every job $j$ runs on a machine of speed $\bar s_{k(j)}$, and (b) whenever, at a time $t \ge 0$, all predecessors of a job $j$ have completed but $j$ has not started, every machine of speed $\bar s_{k(j)}$ is busy at time $t$.
--
--   These are the objects of Theorem 2.1 and of every approximation guarantee in the paper.
--
--   **Formalization Note** Jobs are `Fin n` and machines `Fin m`; the Lean speed-class index `0` is the paper's fastest class $\bar s_1$ (index $\kappa$ is $\bar s_{\kappa+1}$). The classes are computed from the speeds (the strictly decreasing enumeration of the set of speeds), so $m_k \ge 1$ and $\bar s_k > 0$ hold by construction. The algorithm is represented by properties (a) and (b), which every run of it has for every list order and every order of idle machines; (b) is exactly what the proof of Theorem 2.1 uses. The maximum defining $C$ is a `Finset.sup'` over the finite, nonempty set of chains. Positivity $p_j > 0$ is the standard reading of the model.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), pp. 1–2 (§1, model), p. 4 (§2, speed classes, D_k, C, speed-based list scheduling)

import Mathlib

namespace UniformPrecSched.Makespan

/-- An instance of `Q|prec|C_max` (Chudak–Shmoys, §1, p. 1): `n` jobs `0, …, n-1` and `m`
machines `0, …, m-1`; job `j` requires `p j > 0` units of processing, machine `i` runs at speed
`s i > 0`, so job `j` takes `p j / s i` time units on machine `i`. The precedence constraints
are a strict partial order `prec` on the jobs: `prec j k` means `j ≺ k`, i.e. job `k` may not
start until job `j` has been completed. There is at least one machine. -/
structure Instance (n m : ℕ) where
  /-- processing requirements `p_j` -/
  p : Fin n → ℝ
  /-- machine speeds `s_i` -/
  s : Fin m → ℝ
  /-- the precedence relation: `prec j k` means `j ≺ k` -/
  prec : Fin n → Fin n → Prop
  m_pos : 0 < m
  p_pos : ∀ j, 0 < p j
  s_pos : ∀ i, 0 < s i
  prec_irrefl : ∀ j, ¬ prec j j
  prec_trans : ∀ i j k, prec i j → prec j k → prec i k

variable {n m : ℕ}

/-- A feasible nonpreemptive schedule (§1, pp. 1–2): job `j` is processed without interruption
on machine `μ j`, starting at time `S j ≥ 0` and completing at `S j + p j / s (μ j)`; two
different jobs on the same machine are not processed at the same time; and if `j ≺ k` then `k`
starts no earlier than `j` completes. -/
structure Schedule (I : Instance n m) where
  /-- the machine processing each job -/
  μ : Fin n → Fin m
  /-- start times -/
  S : Fin n → ℝ
  S_nonneg : ∀ j, 0 ≤ S j
  noOverlap : ∀ i j, i ≠ j → μ i = μ j →
    S i + I.p i / I.s (μ i) ≤ S j ∨ S j + I.p j / I.s (μ j) ≤ S i
  precedence : ∀ i j, I.prec i j → S i + I.p i / I.s (μ i) ≤ S j

/-- Completion time `C_j = S_j + p_j / s_{μ(j)}` of job `j`. -/
noncomputable def Schedule.C {I : Instance n m} (σ : Schedule I) (j : Fin n) : ℝ :=
  σ.S j + I.p j / I.s (σ.μ j)

/-- The length of a schedule, `C_max = max_j C_j` (p. 1), and `0` when there are no jobs. -/
noncomputable def Schedule.makespan {I : Instance n m} (σ : Schedule I) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.sup' h σ.C else 0

/-- The set of distinct machine speeds. -/
noncomputable def speedSet (I : Instance n m) : Finset ℝ :=
  Finset.univ.image I.s

/-- `K`, the number of distinct machine speeds (p. 4, Theorem 3.5). -/
noncomputable def numSpeeds (I : Instance n m) : ℕ :=
  (speedSet I).card

/-- The distinct speeds `s̄_1 > s̄_2 > ⋯ > s̄_K` (p. 4), as a function on `Fin K`; the Lean index
`0` is the paper's fastest class `s̄_1`, and in general Lean index `κ` is the paper's
`s̄_{κ+1}`. It is the strictly decreasing enumeration of the set of machine speeds. -/
noncomputable def classSpeed (I : Instance n m) (κ : Fin (numSpeeds I)) : ℝ :=
  (speedSet I).orderEmbOfFin rfl (Fin.rev κ)

/-- `m_k`, the number of machines of speed `s̄_k` (p. 4). -/
noncomputable def classCount (I : Instance n m) (κ : Fin (numSpeeds I)) : ℕ :=
  (Finset.univ.filter fun i => I.s i = classSpeed I κ).card

/-- A job assignment `k(j)` (p. 4): for each job, the index of the speed class at which it is
to be processed. -/
abbrev Assignment (I : Instance n m) : Type :=
  Fin n → Fin (numSpeeds I)

/-- The total load `D_k = (1/m_k) Σ_{j : k(j) = k} p_j / s̄_k` assigned to the machines of speed
`s̄_k` by the assignment `k` (p. 4). -/
noncomputable def classLoad (I : Instance n m) (k : Assignment I) (κ : Fin (numSpeeds I)) : ℝ :=
  (1 / (classCount I κ : ℝ)) *
    ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / classSpeed I κ

/-- The length `Σ_{j ∈ 𝒞} p_j / s̄_{k(j)}` of a set of jobs `𝒞` under the assignment `k`
(p. 4). -/
noncomputable def chainLength (I : Instance n m) (k : Assignment I) (c : Finset (Fin n)) : ℝ :=
  ∑ j ∈ c, I.p j / classSpeed I (k j)

/-- A chain of jobs `j₁ ≺ j₂ ≺ ⋯ ≺ j_r` (pp. 3, 7): since `≺` is transitive, a set of jobs any
two of which are comparable under `≺`. -/
def IsJobChain (I : Instance n m) (c : Finset (Fin n)) : Prop :=
  IsChain I.prec (c : Set (Fin n))

open Classical in
/-- The set of all chains of jobs (finite; it contains the empty chain). -/
noncomputable def chains (I : Instance n m) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun c => IsJobChain I c

theorem chains_nonempty (I : Instance n m) : (chains I).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  unfold chains
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by simp [IsJobChain, IsChain]⟩

/-- `C`, the maximum over all chains `𝒞` of `Σ_{j ∈ 𝒞} p_j / s̄_{k(j)}` (p. 4). The empty chain
contributes `0`. -/
noncomputable def chainBound (I : Instance n m) (k : Assignment I) : ℝ :=
  (chains I).sup' (chains_nonempty I) (chainLength I k)

/-- The schedule `σ` is a schedule that the speed-based list scheduling algorithm of p. 4 can
produce for the assignment `k`, characterized by the two properties of it that the paper uses:
1. every job `j` is processed on a machine of speed `s̄_{k(j)}`;
2. no machine of speed `s̄_{k(j)}` is idle while job `j` is waiting: if at time `t ≥ 0` all
   predecessors of `j` have completed and `j` has not started, then every machine `i` of speed
   `s̄_{k(j)}` is busy at `t`, i.e. some job `j'` on `i` has `S_{j'} ≤ t < C_{j'}`.
This holds for every list order and every order in which idle machines are considered. -/
def IsSpeedListSchedule (I : Instance n m) (k : Assignment I) (σ : Schedule I) : Prop :=
  (∀ j, I.s (σ.μ j) = classSpeed I (k j)) ∧
  ∀ (t : ℝ) (i : Fin m) (j : Fin n), 0 ≤ t → I.s i = classSpeed I (k j) →
    (∀ j', I.prec j' j → σ.C j' ≤ t) → t < σ.S j →
    ∃ j', σ.μ j' = i ∧ σ.S j' ≤ t ∧ t < σ.C j'

end UniformPrecSched.Makespan


