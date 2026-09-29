-- Prove2me | Definitions.Def_ResourceScheduling_Graph_Model
-- name    : ResourceScheduling_Graph_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:19:29.425969+00:00
-- url     : https://prove2.me/theorems/e01ff303-845b-4c5a-ac22-488e61e8e7d7
-- title:
--   Unit-time scheduling on uniform machines with resource constraints (Section 2, Appendix)
-- statement:
--   This module fixes the scheduling model of Błażewicz, Lenstra and Rinnooy Kan for single-operation problems with unit processing times.
--
--   There are $n$ jobs $J_1,\dots,J_n$ and $m$ machines $M_1,\dots,M_m$; "each machine can handle at most one job at a time and each job can be executed by at most one machine at a time". Machine $M_i$ has a speed $q_i>0$, and every job has unit execution requirement $p_j=1$, so its processing time on $M_i$ is $p_{ij}=p_j/q_i=1/q_i$ (parallel uniform machines; identical machines are the case $q_i=1$).
--
--   "Suppose that there are $l$ resources $R_1,\dots,R_l$. For each resource $R_h$, there is a positive integer size $s_h$ which is the total amount of $R_h$ available at any given time. [...] there is for each resource $R_h$ and job $J_j$ a nonnegative integer requirement $r_{hj}$ which is the amount of $R_h$ required by $J_j$ at all times during its execution." A set $S$ of jobs is *resource feasible* if
--   $$\sum_{j\in S} r_{hj}\le s_h\qquad(h=1,\dots,l).$$
--   Precedence constraints are the arcs of a directed acyclic graph $H$ on the jobs; if $H$ contains a directed path from $j$ to $k$, $J_j$ must be completed before $J_k$ can start.
--
--   A (nonpreemptive) schedule assigns each job $J_j$ a machine $\mu(j)$ and a start time $S_j$; its completion time is $C_j=S_j+1/q_{\mu(j)}$, and $J_j$ is being executed at time $t$ when $S_j\le t<C_j$. A schedule is *feasible* when all start times are nonnegative, two distinct jobs on the same machine have disjoint execution intervals, precedence constraints are respected, and "at any time $t$ the index set $S_t$ of jobs being executed at $t$" is resource feasible. The makespan is $C_{\max}=\max_j C_j$ ($C_{\max}=0$ when there are no jobs). The *decision version* of $\alpha\,|\,\beta\,|\,C_{\max}$ with threshold $y$ asks whether a feasible schedule with $C_{\max}\le y$ exists.
--
--   The module also names the resource type $res{\cdot}11$ (every size equals $1$, every requirement is at most $1$, the number of resources is part of the input) and the absence of precedence constraints.
--
--   **Formalization Note.** Jobs, machines and resources are indexed from $0$ (`Fin n`, `Fin m`, `Fin l`). Start times are arbitrary nonnegative reals (a job on a machine of speed $2$ may start at a half-integer), execution intervals are half-open, and the resource constraints are imposed at every real time $t$, not only at integer or start times. Precedence is the transitive closure of the arcs of $H$, which gives the same feasible schedules as requiring each arc.
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

namespace ResourceScheduling.Graph

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

/-- The resource type `res·11`: the number of resources is part of the input, every resource size
equals 1, and every requirement is at most 1. -/
def IsResDot11 : Prop :=
  (∀ h, I.s h = 1) ∧ ∀ h j, I.r h j ≤ 1

/-- No precedence constraints (`β₃ = ∘`): `H` has no arcs. -/
def NoPrecedence : Prop :=
  ∀ j k, ¬ I.arc j k

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

/-- The decision version of `α | β | C_max`: there is a feasible schedule with `C_max ≤ y`. -/
def Instance.HasScheduleWithin (I : Instance) (y : ℝ) : Prop :=
  ∃ σ : Schedule I, σ.Feasible ∧ σ.makespan ≤ y

end ResourceScheduling.Graph


