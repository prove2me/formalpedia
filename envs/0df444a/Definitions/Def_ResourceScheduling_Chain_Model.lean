-- Prove2me | Definitions.Def_ResourceScheduling_Chain_Model
-- name    : ResourceScheduling_Chain_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:22:40.032681+00:00
-- url     : https://prove2.me/theorems/50654052-c246-4494-9d32-5f587bd70bb7
-- title:
--   Unit-time jobs on parallel identical machines with resources and precedence: instances, schedules, feasibility, makespan
-- statement:
--   This file sets up the scheduling model of Błażewicz, Lenstra and Rinnooy Kan for parallel identical machines and unit-time jobs.
--
--   **Instances.** There are $n$ jobs $J_1,\dots,J_n$ and $m$ machines $M_1,\dots,M_m$. "Each machine can handle at most one job at a time and each job can be executed by at most one machine at a time." Every job has processing time $p_j = 1$ on every machine (parallel identical machines, unit processing times). There are $l$ resources $R_1,\dots,R_l$: for each resource $R_h$ "there is a positive integer size $s_h$ which is the total amount of $R_h$ available at any given time", and for each resource $R_h$ and job $J_j$ "a nonnegative integer requirement $r_{hj}$ which is the amount of $R_h$ required by $J_j$ at all times during its execution". Precedence constraints are given by a directed graph $H$ on the jobs, listed by its arcs: "if $H$ contains a directed path from $j$ to $k$, we write $J_j \to J_k$ and require that $J_j$ is completed before $J_k$ can start." The graph $H$ is *acyclic* if no job precedes itself, and *chain-like* if every vertex of $H$ has indegree and outdegree at most one.
--
--   **Schedules.** A (nonpreemptive) schedule assigns to every job $J_j$ a machine $\mu_j$ and a real start time $S_j$; the job is executed during $[S_j, S_j+1)$ and completes at $C_j = S_j + 1$. The schedule is *feasible* when
--
--   1. every start time is nonnegative;
--   2. two distinct jobs on the same machine are not executed at the same time: $C_j \le S_k$ or $C_k \le S_j$;
--   3. $J_j \to J_k$ implies $C_j \le S_k$;
--   4. at any time $t \in \mathbb{R}$, the index set $S_t$ of jobs being executed at $t$ satisfies
--   $$\sum_{j\in S_t} r_{hj} \le s_h \qquad (h = 1,\dots,l).$$
--
--   The makespan is $C_{\max} = \max\{C_1,\dots,C_n\}$ (and $0$ when there are no jobs). The decision version of the $C_{\max}$ problem asks, for a threshold $y\in\mathbb{N}$, whether some feasible schedule has $C_{\max} \le y$.
--
--   These are the objects every statement of the mission is about: the problem classes $P2\mid res111, chain, p_j=1\mid C_{\max}$ and $P3\mid res1\cdot\cdot, p_j=1\mid C_{\max}$ are subclasses of these instances.
--
--   **Formalization Note.** Jobs are `Fin n` and machines `Fin m`, 0-based ($J_{j+1}$ is index `j`). Start times are real numbers and execution intervals are half-open, so a job ending at time $5$ and a job starting at $5$ never overlap; the resource condition is imposed at every real time $t$, not only at integer times. The relation $J_j \to J_k$ is the transitive closure of the arc relation of $H$; requiring the precedence condition on arcs only would be equivalent. Only identical machines are modelled: there are no speeds, since every processing time is $1$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 12–13, Section 2; pp. 22–23, Appendix

import Mathlib

/-!
# Unit-time scheduling on parallel identical machines with resource constraints

Błażewicz, Lenstra & Rinnooy Kan, *Scheduling subject to resource constraints: classification and
complexity*, Discrete Appl. Math. 5 (1983), pp. 12–13 (Section 2) and pp. 22–23 (Appendix),
specialised to parallel identical machines (`α₁ = P`), unit processing times (`p_j = 1`) and no
preemption (`β₁ = ∘`).

Conventions: jobs are `Fin n` and machines `Fin m` (0-based: job `J_{j+1}` is `j`); start times
are real numbers; job `j` is executed during the half-open interval `[S_j, S_j + 1)`.
-/

namespace ResourceScheduling.Chain

/-- An instance of a single-operation problem on `m` parallel identical machines with `n` unit-time
jobs, `l` resources of sizes `s h`, requirements `r h j` of job `j` for resource `h`, and the
precedence digraph `H` given by its list of arcs. -/
structure Instance where
  /-- number of jobs -/
  n : ℕ
  /-- number of machines -/
  m : ℕ
  /-- number of resources -/
  l : ℕ
  /-- resource sizes `s_h` -/
  s : Fin l → ℕ
  /-- resource requirements `r_hj` -/
  r : Fin l → Fin n → ℕ
  /-- the arcs of the precedence digraph `H` -/
  arcs : List (Fin n × Fin n)

namespace Instance

variable (I : Instance)

/-- `(j, k)` is an arc of `H`. -/
def Arc (j k : Fin I.n) : Prop := (j, k) ∈ I.arcs

/-- `J_j → J_k`: `H` contains a directed path (of positive length) from `j` to `k`. -/
def Prec (j k : Fin I.n) : Prop := Relation.TransGen I.Arc j k

/-- `H` is acyclic. -/
def Acyclic : Prop := ∀ j, ¬ I.Prec j j

/-- `β₃ = chain`: every vertex of `H` has indegree and outdegree at most one. -/
def IsChain : Prop :=
  ∀ v : Fin I.n,
    (Finset.univ.filter fun u => (u, v) ∈ I.arcs).card ≤ 1 ∧
    (Finset.univ.filter fun w => (v, w) ∈ I.arcs).card ≤ 1

/-- Every resource size is a positive integer. -/
def SizesPositive : Prop := ∀ h, 0 < I.s h

end Instance

/-- A nonpreemptive schedule: a machine and a real start time for every job. -/
structure Schedule (I : Instance) where
  /-- the machine processing each job -/
  machine : Fin I.n → Fin I.m
  /-- the start time `S_j` of each job -/
  start : Fin I.n → ℝ

namespace Schedule

variable {I : Instance} (σ : Schedule I)

/-- The completion time `C_j = S_j + 1` (unit processing time). -/
def completion (j : Fin I.n) : ℝ := σ.start j + 1

/-- Job `j` is being executed at time `t`, i.e. `t ∈ [S_j, S_j + 1)`. -/
def IsExecutedAt (j : Fin I.n) (t : ℝ) : Prop := σ.start j ≤ t ∧ t < σ.start j + 1

open Classical in
/-- Feasibility: nonnegative start times; two distinct jobs on the same machine do not overlap;
`J_j → J_k` implies `C_j ≤ S_k`; and at every real time `t`, for every resource `h`, the jobs being
executed at `t` require at most `s_h` in total. -/
def Feasible : Prop :=
  (∀ j, 0 ≤ σ.start j) ∧
  (∀ j k, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j) ∧
  (∀ j k, I.Prec j k → σ.completion j ≤ σ.start k) ∧
  (∀ (t : ℝ) (h : Fin I.l),
      ∑ j ∈ Finset.univ.filter (fun j => σ.IsExecutedAt j t), I.r h j ≤ I.s h)

/-- The makespan `C_max = max_j C_j`, with `C_max = 0` when there are no jobs. -/
noncomputable def cmax : ℝ :=
  if h : 0 < I.n then Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ σ.completion else 0

end Schedule

/-- The decision version: some feasible schedule has `C_max ≤ y`. -/
def Instance.HasScheduleWithin (I : Instance) (y : ℕ) : Prop :=
  ∃ σ : Schedule I, σ.Feasible ∧ σ.cmax ≤ (y : ℝ)

end ResourceScheduling.Chain


