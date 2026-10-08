-- Prove2me | Definitions.Def_ProjSchedTW_ActiveSchedules_Project
-- name    : ProjSchedTW_ActiveSchedules_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T15:40:38.600556+00:00
-- url     : https://prove2.me/theorems/3da9dae3-fdf1-4660-aea4-1c479b5ba60b
-- title:
--   §1.3, §2.1, §2.3 — project network, feasible region, schedule-induced orders and order polyhedra
-- statement:
--   This file sets up the resource-constrained project scheduling problem $PS|temp|C_{\max}$ with general time lags, as in Chapters 1 and 2 of Neumann, Schwindt and Zimmermann.
--
--   1. **Project.** The activity set is $V=\{0,1,\dots,n+1\}$; $0$ is the project beginning and $n+1$ the project completion, and $1,\dots,n$ are the real activities. The project network $N$ has arc set $E\subseteq V\times V$ without loops and integer arc weights $\delta_{ij}$. Activity $i$ has an integer duration $p_i\ge 0$ with $p_0=p_{n+1}=0$ and $p_i>0$ for the real activities. There is a set $\mathcal R$ of renewable resources; resource $k$ has capacity $R_k\in\mathbb N$ and activity $i$ requires $r_{ik}\in\mathbb Z_{\ge 0}$ units of it, with $r_{ik}\le R_k$ and $r_{0k}=r_{n+1,k}=0$.
--   2. **Time-feasible schedules** (Definition 1.3.1). A schedule is a vector $S=(S_0,\dots,S_{n+1})$ of real start times with $S_0=0$ and $S_i\ge 0$. It is time-feasible if
--   $$S_j-S_i\ \ge\ \delta_{ij}\qquad(\langle i,j\rangle\in E).$$
--   The set of time-feasible schedules is $\mathcal S_T$.
--   3. **Resource feasibility** (Eqs. (2.1.1)–(2.1.4), Definition 2.1.1). The active set at time $t$ is $\mathcal A(S,t)=\{i\in V\mid S_i\le t<S_i+p_i\}$ and $r_k(S,t)=\sum_{i\in\mathcal A(S,t)}r_{ik}$. A schedule is resource-feasible if $r_k(S,t)\le R_k$ for all $k\in\mathcal R$ and all $t\ge 0$; these schedules form $\mathcal S_R$. The feasible region is $\mathcal S=\mathcal S_T\cap\mathcal S_R$. An optimal schedule is a feasible schedule minimizing $S_{n+1}$ over $\mathcal S$.
--   4. **Schedule-induced order** (Definition 2.3.5): $O(S)=\{(i,j)\in V\times V\mid i\ne j,\ S_j\ge S_i+p_i\}$.
--   5. **Strict orders and order polyhedra** (Definition 2.3.1). A strict order in $V$ is an asymmetric, transitive relation $O\subseteq V\times V$. Its order polyhedron is
--   $$\mathcal S_T(O)=\{S\in\mathcal S_T\mid S_j\ge S_i+p_i\ \text{for all }(i,j)\in O\}.$$
--   $O$ is time-feasible if $\mathcal S_T(O)\neq\emptyset$, and feasible if moreover $\mathcal S_T(O)\subseteq\mathcal S$. The polyhedron $\mathcal S_T(O(S))$ is the schedule polyhedron of $S$.
--   6. **Lower bound** (§2.4, p. 42): for a set $\mathcal M$ of schedules, $lb\,\mathcal M=(\inf_{S\in\mathcal M}S_0,\dots,\inf_{S\in\mathcal M}S_{n+1})$.
--   7. **Duration bound** (Eq. (2.1.3)): $\bar d=\sum_{i\in V}\max\bigl(p_i,\max_{\langle i,j\rangle\in E}\delta_{ij}\bigr)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Activities are `Fin (n + 2)`, with `0` and `Fin.last (n + 1)` the fictitious activities. Start times are real. The resource constraints are imposed for every $t\ge 0$, not only for $0\le t\le\bar d$ as (2.1.4) writes; this is the reading the book's proofs use. The infima in $lb$ are real `sInf`s, meaningful for nonempty sets of schedules (which are bounded below by $0$). In $\bar d$, a node without outgoing arcs contributes $p_i$ (the inner maximum over the empty set is dropped).
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 10, Definition 1.3.1; pp. 24–25, §2.1, Eqs. (2.1.1)–(2.1.4), Definition 2.1.1; pp. 30–32, Definitions 2.3.1, 2.3.5; p. 42 (lb); p. 117, Proposition 2.10.2 (d̄)

import Mathlib

namespace ProjSchedTW.ActiveSchedules

/-- Neumann, Schwindt & Zimmermann, *Project Scheduling with Time Windows and Scarce Resources*,
2nd ed., §1.1–1.2 and §2.1 (pp. 1–7, 24–25). A project with activities
`V = {0, 1, …, n+1}` (`Fin (n + 2)`; `0` is the project beginning, `Fin.last (n+1)` the project
completion), an AoN network with arc set `E` and integer arc weights `δ i j`, integer durations
`p i` (zero for the two fictitious activities, positive for the real activities `1, …, n`), and
renewable resources `k ∈ K` with integer capacities `R k` and requirements `r i k ≤ R k`
(zero for the fictitious activities). -/
structure Project (n : ℕ) (K : Type) where
  /-- The arc set `E` of the project network `N`. -/
  E : Finset (Fin (n + 2) × Fin (n + 2))
  /-- The arc weights `δ_ij` (only their values on arcs of `E` matter). -/
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  /-- The durations `p_i`. -/
  p : Fin (n + 2) → ℕ
  /-- The resource capacities `R_k`. -/
  R : K → ℕ
  /-- The resource requirements `r_ik`. -/
  r : Fin (n + 2) → K → ℕ
  /-- The network has no loops. -/
  no_loop : ∀ e ∈ E, e.1 ≠ e.2
  /-- `p_0 = 0`. -/
  p_zero : p 0 = 0
  /-- `p_{n+1} = 0`. -/
  p_last : p (Fin.last (n + 1)) = 0
  /-- `p_i > 0` for the real activities `i = 1, …, n`. -/
  p_pos : ∀ i : Fin (n + 2), i ≠ 0 → i ≠ Fin.last (n + 1) → 0 < p i
  /-- `r_{0k} = 0`. -/
  r_zero : ∀ k, r 0 k = 0
  /-- `r_{n+1,k} = 0`. -/
  r_last : ∀ k, r (Fin.last (n + 1)) k = 0
  /-- `r_ik ≤ R_k`. -/
  r_le : ∀ i k, r i k ≤ R k

variable {n : ℕ} {K : Type}

/-- Definition 1.3.1 and Eq. (1.2.1) (p. 10): the set `S_T` of time-feasible schedules, i.e.
vectors `S = (S_0, …, S_{n+1})` of real start times with `S_0 = 0`, `S_i ≥ 0` and
`S_j − S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E`. -/
def timeFeasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  {S | S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1}

/-- Eq. (2.1.1) (p. 25): the active set `A(S, t) = {i ∈ V | S_i ≤ t < S_i + p_i}`. -/
noncomputable def activeSet (P : Project n K) (S : Fin (n + 2) → ℝ) (t : ℝ) :
    Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter (fun i => S i ≤ t ∧ t < S i + (P.p i : ℝ))

/-- Eq. (2.1.2) (p. 25): the amount `r_k(S, t) = ∑_{i ∈ A(S,t)} r_ik` of resource `k` used at
time `t`. -/
noncomputable def usage (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) (t : ℝ) : ℕ :=
  ∑ i ∈ activeSet P S t, P.r i k

/-- Definition 2.1.1 with the resource constraints (2.1.4) (p. 25): the set `S_R` of
resource-feasible schedules (`S_0 = 0`, `S ≥ 0`, and `r_k(S, t) ≤ R_k` for every resource `k`
and every time `t ≥ 0`). The constraint is imposed for all `t ≥ 0`, as the book's proofs use it,
rather than only for `0 ≤ t ≤ d̄` as (2.1.4) writes. -/
def resourceFeasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  {S | S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ ∀ k, ∀ t : ℝ, 0 ≤ t → usage P S k t ≤ P.R k}

/-- Definition 2.1.1 (p. 25): the feasible region `𝒮 = S_T ∩ S_R`. -/
def feasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  timeFeasibleSet P ∩ resourceFeasibleSet P

/-- Definition 2.1.1 (p. 25): an optimal schedule is a feasible schedule minimizing the project
duration `S_{n+1}` over `𝒮`. -/
def IsOptimal (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ∀ S' ∈ feasibleSet P, S (Fin.last (n + 1)) ≤ S' (Fin.last (n + 1))

/-- Definition 2.3.5 (p. 32): the schedule-induced strict order
`O(S) = {(i, j) ∈ V × V | i ≠ j, S_j ≥ S_i + p_i}`. -/
def scheduleOrder (P : Project n K) (S : Fin (n + 2) → ℝ) : Set (Fin (n + 2) × Fin (n + 2)) :=
  {e | e.1 ≠ e.2 ∧ S e.1 + (P.p e.1 : ℝ) ≤ S e.2}

/-- A strict order in the activity set `V`: an asymmetric and transitive relation
(§1.4, used in Definition 2.3.1, p. 30). -/
def IsStrictOrderRel (O : Set (Fin (n + 2) × Fin (n + 2))) : Prop :=
  (∀ i j, (i, j) ∈ O → (j, i) ∉ O) ∧ (∀ i j l, (i, j) ∈ O → (j, l) ∈ O → (i, l) ∈ O)

/-- Definition 2.3.1 (p. 30): the order polyhedron
`S_T(O) = {S ∈ S_T | S_j ≥ S_i + p_i for all (i, j) ∈ O}`. -/
def orderPolyhedron (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2))) :
    Set (Fin (n + 2) → ℝ) :=
  {S | S ∈ timeFeasibleSet P ∧ ∀ e ∈ O, S e.1 + (P.p e.1 : ℝ) ≤ S e.2}

/-- Definition 2.3.1 (p. 30): a strict order `O` is feasible if it is time-feasible
(`S_T(O) ≠ ∅`) and `S_T(O) ⊆ 𝒮`. -/
def IsFeasibleOrder (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2))) : Prop :=
  IsStrictOrderRel O ∧ (orderPolyhedron P O).Nonempty ∧ orderPolyhedron P O ⊆ feasibleSet P

/-- §2.4, p. 42: the lower bound `lb M = (inf_{S ∈ M} S_0, …, inf_{S ∈ M} S_{n+1})` of a set `M`
of schedules (the vector of componentwise infima; a real infimum, meaningful when `M` is
nonempty and bounded below, e.g. `M ⊆ ℝ^{n+2}_{≥0}`). -/
noncomputable def lowerBound (M : Set (Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ :=
  fun i => sInf ((fun S => S i) '' M)

/-- Eq. (2.1.3) (p. 25) and Proposition 2.10.2 (p. 117):
`d̄ = ∑_{i ∈ V} max(p_i, max_{⟨i,j⟩ ∈ E} δ_ij)`. For a node `i` without outgoing arcs the inner
maximum is over the empty set and the term is `p_i`. -/
def dbar (P : Project n K) : ℤ := by
  classical
  exact ∑ i, (insert (P.p i : ℤ) ((P.E.filter (fun e => e.1 = i)).image
    (fun e => P.δ e.1 e.2))).max' (Finset.insert_nonempty _ _)

end ProjSchedTW.ActiveSchedules


