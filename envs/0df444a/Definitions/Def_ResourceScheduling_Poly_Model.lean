-- Prove2me | Definitions.Def_ResourceScheduling_Poly_Model
-- name    : ResourceScheduling_Poly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:28:41.312457+00:00
-- url     : https://prove2.me/theorems/98f7d9dd-1c39-4278-9ac0-ba9c1da0cfab
-- title:
--   Unit-time scheduling on uniform machines with resource constraints: instances, schedules, feasibility, makespan (Section 2, Appendix)
-- statement:
--   This is the scheduling model of Błażewicz, Lenstra and Rinnooy Kan for single-operation problems with unit processing times and scarce resources.
--
--   An **instance** consists of $n$ jobs $J_1,\dots,J_n$ and $m$ parallel uniform machines $M_1,\dots,M_m$, machine $M_i$ having speed $q_i>0$. Every job has unit execution requirement $p_j=1$, so that it takes time $p_{ij}=1/q_i$ on $M_i$ ("Q (parallel uniform machines): $p_{ij}=p_j/q_i$", Appendix); identical machines ($P$) are the case $q_i=1$. There are $l$ resources $R_1,\dots,R_l$: "For each resource $R_h$, there is a positive integer size $s_h$ which is the total amount of $R_h$ available at any given time", and "for each resource $R_h$ and job $J_j$ a nonnegative integer requirement $r_{hj}$ which is the amount of $R_h$ required by $J_j$ at all times during its execution". Precedence constraints are given by an acyclic directed graph $H$ on the jobs, $J_j\to J_k$ meaning that $H$ contains a directed path from $J_j$ to $J_k$.
--
--   A (nonpreemptive) **schedule** assigns each job $J_j$ a machine $\mu(j)$ and a real start time $S_j$; the job is being executed at time $t$ when $t\in[S_j,C_j)$, where
--   $$C_j=S_j+\frac{1}{q_{\mu(j)}}.$$
--   It is **feasible** when every $S_j\ge 0$; two different jobs on the same machine have disjoint execution intervals; $J_j\to J_k$ implies $C_j\le S_k$; and "at any time $t$ the index set $S_t$ of jobs being executed at $t$ satisfies $\sum_{j\in S_t} r_{hj}\le s_h$ ($h=1,\dots,l$)". The **makespan** is $C_{\max}=\max_j C_j$.
--
--   The definition also records two predicates on instances: *no precedence constraints* ($H$ has no arcs) and *every job fits alone* ($r_{hj}\le s_h$ for all $h,j$).
--
--   This model is shared by every statement of the mission: the optimality of the two-machine algorithm (Theorem 5), the matching characterization for two identical machines (Theorem 1) and the bottleneck transportation formulation (Theorem 6).
--
--   **Formalization Note** Jobs, machines and resources are indexed by `Fin n`, `Fin m`, `Fin l` (0-based). Start times are arbitrary nonnegative reals, execution intervals are half-open, and the resource constraints are checked at every real time $t$, not only at integer times. $C_{\max}$ is defined as $0$ when $n=0$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 12–13, Section 2; pp. 22–23, Appendix

import Mathlib

/-!
# Single-operation scheduling with unit-time jobs and resource constraints

Błażewicz, Lenstra & Rinnooy Kan, *Scheduling subject to resource constraints: classification and
complexity*, Discrete Appl. Math. 5 (1983), pp. 12–13 (Section 2) and pp. 22–23 (Appendix).

Jobs are `Fin n` (the paper's `J_1, …, J_n`, 0-based here), machines are `Fin m`
(`M_1, …, M_m`), resources are `Fin l` (`R_1, …, R_l`). Every job has unit execution requirement
`p_j = 1`, so its processing time on machine `M_i` of speed `q_i` is `1 / q_i` (parallel uniform
machines; identical machines are the case `q = 1`). Schedules are nonpreemptive; a job occupies
the half-open interval `[S_j, S_j + 1/q_{μ(j)})` of its machine, and the resource constraints are
checked at every real time `t`.
-/

namespace ResourceScheduling.Poly

/-- An instance of a single-operation, unit-time scheduling problem on parallel uniform machines
with resource constraints and precedence constraints (Section 2 and Appendix). -/
structure Instance where
  /-- Number of jobs `n`. -/
  n : ℕ
  /-- Number of machines `m`. -/
  m : ℕ
  /-- Speed `q_i` of machine `M_i`. -/
  q : Fin m → ℝ
  q_pos : ∀ i, 0 < q i
  /-- Number of resources `l`. -/
  l : ℕ
  /-- Size `s_h` of resource `R_h`: a positive integer. -/
  s : Fin l → ℕ
  s_pos : ∀ h, 0 < s h
  /-- Requirement `r_{hj}` of job `J_j` for resource `R_h`: a nonnegative integer. -/
  r : Fin l → Fin n → ℕ
  /-- The arcs of the precedence digraph `H`. -/
  arc : Fin n → Fin n → Prop
  /-- `H` is acyclic. -/
  acyclic : ∀ j, ¬ Relation.TransGen arc j j

namespace Instance

variable (I : Instance)

/-- Processing time `p_{ij} = p_j / q_i = 1 / q_i` of a unit-time job on machine `M_i`. -/
noncomputable def procTime (i : Fin I.m) : ℝ := 1 / I.q i

/-- A set `S` of jobs is resource feasible: `∑_{j ∈ S} r_{hj} ≤ s_h` for `h = 1, …, l`. -/
def ResourceFeasibleSet (S : Finset (Fin I.n)) : Prop :=
  ∀ h : Fin I.l, ∑ j ∈ S, I.r h j ≤ I.s h

/-- No precedence constraints (`β₃ = ∘`): `H` has no arcs. -/
def NoPrecedence : Prop :=
  ∀ j k, ¬ I.arc j k

/-- Every job fits alone: `r_{hj} ≤ s_h` for every resource `R_h` and job `J_j`. -/
def EveryJobFits : Prop :=
  ∀ h j, I.r h j ≤ I.s h

end Instance

/-- A nonpreemptive schedule: each job `J_j` is processed on machine `machine j` starting at the
real time `start j`. -/
structure Schedule (I : Instance) where
  machine : Fin I.n → Fin I.m
  start : Fin I.n → ℝ

namespace Schedule

variable {I : Instance} (σ : Schedule I)

/-- Completion time `C_j = S_j + 1 / q_{μ(j)}`. -/
noncomputable def completion (j : Fin I.n) : ℝ :=
  σ.start j + I.procTime (σ.machine j)

/-- Job `J_j` is being executed at time `t`: `t ∈ [S_j, C_j)`. -/
def IsExecutingAt (j : Fin I.n) (t : ℝ) : Prop :=
  σ.start j ≤ t ∧ t < σ.completion j

/-- The index set `S_t` of jobs being executed at time `t`. -/
noncomputable def activeSet (t : ℝ) : Finset (Fin I.n) := by
  classical
  exact Finset.univ.filter fun j => σ.IsExecutingAt j t

/-- Feasibility of a schedule: start times are nonnegative; each machine handles at most one job
at a time; `J_j → J_k` (a directed path in `H`) forces `J_j` to complete before `J_k` starts;
and at every real time `t` the set `S_t` of jobs being executed satisfies every resource
constraint. -/
def Feasible : Prop :=
  (∀ j, 0 ≤ σ.start j) ∧
  (∀ j k, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j) ∧
  (∀ j k, Relation.TransGen I.arc j k → σ.completion j ≤ σ.start k) ∧
  (∀ t : ℝ, I.ResourceFeasibleSet (σ.activeSet t))

/-- The makespan `C_max = max_j C_j`, with `C_max = 0` when there are no jobs. -/
noncomputable def makespan : ℝ :=
  if h : (Finset.univ : Finset (Fin I.n)).Nonempty then Finset.univ.sup' h σ.completion else 0

end Schedule

end ResourceScheduling.Poly


