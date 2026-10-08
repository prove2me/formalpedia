-- Prove2me | Definitions.Def_SchedComplexity_PrecChain_Model
-- name    : SchedComplexity_PrecChain_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:50:21.334222+00:00
-- url     : https://prove2.me/theorems/5f77e45f-ffc8-40e6-b434-b8f7496327ce
-- title:
--   Single-operation jobs on m identical machines with precedence constraints: the class n|m|I,prec,1≤p_j1≤p_*, schedules, C_max and Σ C_j
-- statement:
--   The model of Section 3 of Brucker, Lenstra & Rinnooy Kan for a parallel shop ($\ell = I$) with precedence constraints. An **instance** consists of $n$ jobs $J_1,\dots,J_n$, a number $m$ of identical machines $M_1,\dots,M_m$, a processing time $p_j \in \mathbb N$ for each job (each job is a single operation, processed on any one machine), and a precedence relation $<$ on the jobs: $J_j < J_k$ means "$J_j$ precedes $J_k$". All jobs are available at time $0$.
--
--   1. The instance **belongs to the class** $n|m|I,\mathit{prec},1\le p_{j1}\le p_*$ for a constant $p_*$ if $m \ge 1$, every processing time satisfies $1 \le p_j \le p_*$, and the precedence relation is **acyclic**: there is no chain $J_j < J_{k_1} < \dots < J_j$.
--   2. A **schedule** assigns to each job $J_j$ a machine and a starting time $B_j \in \mathbb N$; its completion time is $C_j = B_j + p_j$.
--   3. A schedule is **feasible** if any two distinct jobs on the same machine are processed one after the other ($C_j \le B_k$ or $C_k \le B_j$), and $J_j < J_k$ implies $C_j \le B_k$. Idle time is allowed.
--   4. The recognition version of the makespan problem asks whether some feasible schedule has
--   $$C_{\max} = \max_{1\le j\le n} C_j \le y,$$
--   and that of the total completion time problem (all weights $w_j = 1$) whether some feasible schedule has $\sum_{j=1}^n C_j \le y$.
--
--   These are the two problems compared in Theorem 1(l).
--
--   **Formalization Note** Jobs and machines are 0-based (`Fin n`, `Fin m`). The precedence relation is a Boolean matrix so that instances can be written down; acyclicity is stated as irreflexivity of its transitive closure. The paper treats `prec` as precedence constraints between the jobs without saying that they are acyclic; a cyclic relation admits no feasible schedule, and the claim "any instance has a solution with $C_{\max} \le n'p_*$" in the proof of Theorem 1(l) needs acyclicity, so it is part of the class here. Likewise $m \ge 1$ is part of the class (the number of machines is at least one). Start times are natural numbers: Section 3 computes $B_j$ and $C_j$ from processing orders on nonnegative integer data, and both criteria are regular, so real start times would give the same yes-instances. "$C_{\max} \le y$" is written as "$C_j \le y$ for every $j$", which agrees with the maximum for $n \ge 1$ and holds for $n = 0$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 4, 6–7, Sections 2–3 (ℓ = I, prec, 1≤p_jr≤p_*, w_j=1, C_max, Σw_jC_j)

import Mathlib

namespace SchedComplexity.PrecChain

/-- An instance of the problem class `n|m|I,prec,1≤p_j1≤p_*|k` of Brucker, Lenstra &
Rinnooy Kan (Report BW 43/75, 1975, Section 3, pp. 6–7), before the class restrictions are
imposed: `n` single-operation jobs `J_j` (`Fin n`, 0-based: the paper's `J_{j+1}` is `j`),
`m` identical parallel machines (`ℓ = I`), the processing time `p j` of each job, and the
precedence relation given as a Boolean matrix: `prec j k = true` means `J_j < J_k`
("`J_j` precedes `J_k`"). Weights, release dates and due dates do not occur: the criteria of
this mission are `C_max` and `Σ_j C_j` (`w_j = 1`), and all jobs are available at time `0`. -/
structure Instance where
  /-- the number of jobs -/
  n : ℕ
  /-- the number of identical machines -/
  m : ℕ
  /-- the processing times `p_j` -/
  p : Fin n → ℕ
  /-- the precedence relation: `prec j k = true` iff `J_j < J_k` -/
  prec : Fin n → Fin n → Bool

namespace Instance

variable (I : Instance)

/-- `J_j < J_k`: job `j` is required to precede job `k`. -/
def Precedes (j k : Fin I.n) : Prop := I.prec j k = true

/-- The precedence relation is acyclic: no job precedes itself through a chain
`J_j < … < J_j` of length at least one. -/
def Acyclic : Prop := ∀ j : Fin I.n, ¬ Relation.TransGen I.Precedes j j

/-- Membership in the class `n|m|I,prec,1≤p_j1≤p_*` for the constant `p_*` (p. 7): at least one
machine, every processing time in `[1, p_*]` (the element `1≤p_jr≤p_*` of `λ`), and acyclic
precedence constraints (the paper's `prec` is a precedence order between the jobs; a cyclic
relation admits no schedule at all). -/
def InClass (pstar : ℕ) : Prop :=
  1 ≤ I.m ∧ (∀ j : Fin I.n, 1 ≤ I.p j ∧ I.p j ≤ pstar) ∧ I.Acyclic

end Instance

/-- A nonpreemptive schedule of an instance `I` on its identical machines: job `j` is processed
on machine `machine j` (`Fin I.m`, 0-based: machine `0` is the paper's `M_1`) from its starting
time `start j = B_j`, a natural number. Start times are natural numbers because Section 3
(p. 6) computes the times `B_j`, `C_j` from processing orders on integer data. -/
structure Schedule (I : Instance) where
  /-- the machine processing each job -/
  machine : Fin I.n → Fin I.m
  /-- the starting time `B_j` of each job -/
  start : Fin I.n → ℕ

namespace Schedule

variable {I : Instance} (σ : Schedule I)

/-- The completion time `C_j = B_j + p_j`. -/
def completion (j : Fin I.n) : ℕ := σ.start j + I.p j

/-- Feasibility (p. 6 and p. 7): two distinct jobs on the same machine are processed one after
the other ("each machine can handle at most one job at a time"), and `J_j < J_k` implies
`C_j ≤ B_k` (the element `prec` of `λ`). Idle time is allowed. -/
def IsFeasible : Prop :=
  (∀ j k : Fin I.n, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j) ∧
    (∀ j k : Fin I.n, I.Precedes j k → σ.completion j ≤ σ.start k)

/-- The total completion time `Σ_j C_j`, i.e. `Σ_j w_j C_j` with `w_j = 1` (p. 7). -/
def totalCompletion : ℕ := ∑ j : Fin I.n, σ.completion j

end Schedule

/-- The yes-instances of the recognition version of `C_max` (Section 2, p. 4): some feasible
schedule has `C_max ≤ y`, written as `C_j ≤ y` for every job `j` (which is `max_j C_j ≤ y` when
`n ≥ 1`, and holds for `n = 0`). -/
def CmaxYes (I : Instance) (y : ℕ) : Prop :=
  ∃ σ : Schedule I, σ.IsFeasible ∧ ∀ j : Fin I.n, σ.completion j ≤ y

/-- The yes-instances of the recognition version of `Σ_j C_j`: some feasible schedule has
`Σ_j C_j ≤ y`. -/
def SumCYes (I : Instance) (y : ℕ) : Prop :=
  ∃ σ : Schedule I, σ.IsFeasible ∧ σ.totalCompletion ≤ y

end SchedComplexity.PrecChain


