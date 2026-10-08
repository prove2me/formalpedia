-- Prove2me | Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
-- name    : UnrelatedSched_TwoApprox_DeadlineLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:36:44.458477+00:00
-- url     : https://prove2.me/theorems/8c6b5cc4-b301-43fb-8dea-fc84cf45e954
-- title:
--   The deadline linear program (LP), its vertices, the integer program (IP) and the support graph (Section 2)
-- statement:
--   There are $n$ jobs and $m$ machines; job $j$ needs $p_{ij}\in\mathbb N$ time units on machine $i$. Fix deadlines $d_1,\dots,d_m\in\mathbb R$ and a threshold $t\in\mathbb R$. Write
--   $$J_i(t)=\{j : p_{ij}\le t\},\qquad M_j(t)=\{i : p_{ij}\le t\}$$
--   for the jobs that machine $i$ can process within $t$ time units and the machines that can process job $j$ within $t$ time units.
--
--   The **linear program (LP)** of the Rounding Theorem asks for real numbers $x_{ij}$, $j\in J_i(t)$, with
--   $$\sum_{i\in M_j(t)}x_{ij}=1\ (j=1,\dots,n),\qquad \sum_{j\in J_i(t)}p_{ij}x_{ij}\le d_i\ (i=1,\dots,m),\qquad x_{ij}\ge 0 .$$
--   Its feasible region is a polytope; a **vertex** of (LP) is an extreme point of this polytope. The **integer program (IP)** has the same job constraints, machine constraints $\sum_{j\in J_i(t)}p_{ij}x_{ij}\le d_i+t$, and $x_{ij}\in\{0,1\}$. A 0-1 solution of (IP) is the same thing as a schedule $\sigma$ (each job $j$ on one machine $\sigma(j)$) with $p_{\sigma(j)j}\le t$ for every job and load $\sum_{j:\sigma(j)=i}p_{ij}\le d_i+t$ on every machine.
--
--   A schedule $\sigma$ is **supported on** a point $\tilde x$ if $\tilde x_{\sigma(j)j}>0$ for every job $j$. The **support graph** of $\tilde x$ is the bipartite graph $G=(M,J,E)$ on machines $M=\{1,\dots,m\}$ and jobs $J=\{1,\dots,n\}$ with edges $E=\{(i,j)\mid \tilde x_{ij}>0\}$. A bipartite edge set $E$ is a **pseudoforest** if every set $S$ of machines and $T$ of jobs spans at most $|S|+|T|$ edges of $E$; equivalently, every connected component has no more edges than nodes. Finally, the 0-1 matrix of a schedule $\sigma$ has $x_{ij}=1$ if $\sigma(j)=i$ and $0$ otherwise.
--
--   These objects are shared by every statement of the mission: the Rounding Theorem, its proof steps and the 2-relaxed decision procedure of Section 3 are written with them.
--
--   **Formalization Note** The paper's variables exist only for $j\in J_i(t)$. Here $x$ is a full real $m\times n$ matrix and the entries with $p_{ij}>t$ are constrained to $0$; the resulting polytope is affinely isomorphic to the paper's (the extra coordinates are fixed at $0$), so its extreme points correspond exactly to the paper's vertices. Deadlines and threshold are real, which is more general than the paper's integers. Loads are the published `MatousekLP.Scheduling.load` of the real matrix $(p_{ij})$. The pseudoforest property is stated in the hereditary counting form, equivalent to the component form for finite graphs.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 3, Section 2 and Theorem 1 ((LP), (IP)); p. 4 (support graph, pseudoforest); p. 5 (0-1 matrix of a schedule)

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- The processing times `p_ij ∈ ℕ` (machine `i`, job `j`) read as real numbers, the form in which
the published `load` and `makespan` take them. -/
def realTimes {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => (P i j : ℝ)

/-- `J_i(t)`: the jobs that require no more than `t` time units on machine `i` (§2, p. 3). -/
noncomputable def jobsWithin {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (t : ℝ) (i : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun j => (P i j : ℝ) ≤ t

/-- `M_j(t)`: the machines that can process job `j` in no more than `t` time units (§2, p. 3). -/
noncomputable def machinesWithin {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (t : ℝ) (j : Fin n) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => (P i j : ℝ) ≤ t

/-- Feasibility for the linear program (LP) of the Rounding Theorem (§2, p. 3) with deadlines
`d_1, …, d_m` and threshold `t`. The paper has a variable `x_ij` only for `j ∈ J_i(t)`; here `x` is a
full `m × n` matrix whose entries with `p_ij > t` are fixed to `0` (`zero_outside`), so the job
constraint `∑_i x_ij = 1` is the paper's `∑_{i ∈ M_j(t)} x_ij = 1` and the machine constraint
`∑_j p_ij x_ij ≤ d_i` is the paper's `∑_{j ∈ J_i(t)} p_ij x_ij ≤ d_i`. -/
structure LPFeasible {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) : Prop where
  zero_outside : ∀ i j, t < (P i j : ℝ) → x i j = 0
  job : ∀ j, ∑ i, x i j = 1
  machine : ∀ i, ∑ j, (P i j : ℝ) * x i j ≤ d i
  nonneg : ∀ i j, 0 ≤ x i j

/-- The feasible region of (LP), a polytope in `ℝ^{m × n}`. -/
def LPPolytope {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {x | LPFeasible P d t x}

/-- `x` is a vertex of (LP): an extreme point of its feasible region. -/
def IsLPVertex {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  x ∈ Set.extremePoints ℝ (LPPolytope P d t)

/-- A 0-1 solution of the integer program (IP) of the Rounding Theorem (§2, p. 3), written as the
schedule `σ` with `x̄_ij = 1 ↔ σ(j) = i`: every job is on exactly one machine, it is only put on a
machine of `M_j(t)`, and machine `i` has load at most `d_i + t`. -/
def IPFeasible {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ)
    (σ : Fin n → Fin m) : Prop :=
  (∀ j, (P (σ j) j : ℝ) ≤ t) ∧ ∀ i, load (realTimes P) σ i ≤ d i + t

/-- The schedule `σ` is supported on `x`: every job goes to a machine `i` with `x_ij > 0`, i.e. along
an edge of the support graph of `x`. -/
def SupportedOn {m n : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) : Prop :=
  ∀ j, 0 < x (σ j) j

/-- The edge set `E = {(i, j) | x_ij > 0}` of the bipartite support graph `G = (M, J, E)` of `x`
(§2, p. 4), with machines `M = Fin m` and jobs `J = Fin n`. -/
noncomputable def supportEdges {m n : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun e => 0 < x e.1 e.2

/-- A bipartite graph between machines and jobs with edge set `E` is a pseudoforest, in counting
form: every set `S` of machines and `T` of jobs spans at most `|S| + |T|` edges. This is equivalent to
the paper's "each connected component has no more edges than nodes" (p. 4): restricting to a
component gives that property, and every induced subgraph of a pseudoforest is a pseudoforest. -/
def IsPseudoforest {m n : ℕ} (E : Finset (Fin m × Fin n)) : Prop :=
  ∀ (S : Finset (Fin m)) (T : Finset (Fin n)),
    (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ T).card ≤ S.card + T.card

/-- The 0-1 matrix of a schedule: `x_ij = 1` if job `j` is assigned to machine `i`, `0` otherwise
(§3, p. 5). -/
def assignmentMatrix {m n : ℕ} (σ : Fin n → Fin m) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if σ j = i then 1 else 0

end UnrelatedSched.TwoApprox


