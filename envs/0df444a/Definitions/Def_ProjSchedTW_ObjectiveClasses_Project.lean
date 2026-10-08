-- Prove2me | Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
-- name    : ProjSchedTW_ObjectiveClasses_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:36.315321+00:00
-- url     : https://prove2.me/theorems/c7c85ec5-e073-4f10-81e5-b8f9dfbc8d3c
-- title:
--   §1.2, §2.1, §3.1 — project network with deadline, feasible region, schedule-induced orders and equal-order sets
-- statement:
--   This file sets up problem $PS|temp,\bar d|f$ of Chapter 3 of Neumann, Schwindt and Zimmermann: resource-constrained project scheduling with general time lags, a prescribed maximum project duration $\bar d$ and an arbitrary objective function $f$.
--
--   1. **Project.** The activity set is $V=\{0,1,\dots,n+1\}$ with $n\ge 1$; $0$ is the project beginning, $n+1$ the project completion, and $1,\dots,n$ are the real activities. The project network $N$ has an arc set $E\subseteq V\times V$ without loops and integer arc weights $\delta_{ij}$. Activity $i$ has an integer duration $p_i$, with $p_0=p_{n+1}=0$ and $p_i>0$ for the real activities. Each renewable resource $k\in\mathcal R$ has a capacity $R_k\in\mathbb N$, and activity $i$ requires $r_{ik}\in\mathbb N$ units of it, with $r_{ik}\le R_k$ and $r_{0k}=r_{n+1,k}=0$. A maximum project duration $\bar d\in\mathbb N$ is prescribed; as in §3.1, the network contains the backward arc $\langle n+1,0\rangle$ with weight $\delta_{n+1,0}=-\bar d$, which encodes $S_{n+1}\le\bar d$. From every node $i$ there is a path to node $n+1$ whose length is at least $p_i$ (p. 8, a consequence of Definition 1.1.1 and Remarks 1.1.2).
--   2. **Time-feasible schedules.** A schedule is a vector $S=(S_0,\dots,S_{n+1})$ of real start times with $S_0=0$ and $S_i\ge 0$. It is time-feasible if
--   $$S_j-S_i\ \ge\ \delta_{ij}\qquad(\langle i,j\rangle\in E).$$
--   These schedules form the time-feasible region $\mathcal S_T$.
--   3. **Resource feasibility.** The active set at time $t$ is $\mathcal A(S,t)=\{i\in V\mid S_i\le t<S_i+p_i\}$ and $r_k(S,t)=\sum_{i\in\mathcal A(S,t)}r_{ik}$. $S$ is resource-feasible if $r_k(S,t)\le R_k$ for all $k\in\mathcal R$ and all $t\ge 0$. The feasible region $\mathcal S$ consists of the schedules that are time- and resource-feasible.
--   4. **Optimal schedules.** For $f:\mathbb R^{n+2}_{\ge 0}\to\mathbb R$, a schedule $S$ is optimal for $PS|temp,\bar d|f$ if $S\in\mathcal S$ and $f(S)\le f(S')$ for every $S'\in\mathcal S$.
--   5. **Orders and polytopes.** The strict order induced by $S$ is $O(S)=\{(i,j)\in V\times V\mid i\ne j,\ S_j\ge S_i+p_i\}$. For a relation $O\subseteq V\times V$ the order polytope is $\mathcal S_T(O)=\{S\in\mathcal S_T\mid S_j\ge S_i+p_i \text{ for all }(i,j)\in O\}$.
--   6. **Equal-order set** (Eq. (3.3.10)). The equal-order set of a schedule $S$ is
--   $$\mathcal S_T^{=}(O(S))=\{S'\in\mathcal S_T(O(S))\mid O(S')=O(S)\}.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Activities are `Fin (n + 2)`, with `0` and `Fin.last (n + 1)` the fictitious activities; start times are real. The deadline is the backward arc of the network, as in the book. The resource constraints are imposed for every $t\ge 0$; because every activity ends by $S_{n+1}\le\bar d$ (the path condition of item 1), this is the book's $0\le t\le\bar d$. Walks in the network are an inductive predicate `NetworkWalk` recording the sum of the arc weights.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, pp. 7–8, Eq. (1.2.1) and the path property on p. 8; pp. 24–25, Eqs. (2.1.1)–(2.1.2); pp. 30–32, Definitions 2.3.1, 2.3.5; p. 197, Eqs. (3.1.1)–(3.1.2); p. 227, Eq. (3.3.10)

import Mathlib

namespace ProjSchedTW.ObjectiveClasses

/-- A directed walk from `i` to `j` of length `w` in the network with arc set `E` and arc
weights `δ` (the length is the sum of the arc weights along the walk; the empty walk from `i`
to `i` has length `0`). -/
inductive NetworkWalk {m : ℕ} (E : Finset (Fin m × Fin m)) (δ : Fin m → Fin m → ℤ) :
    Fin m → Fin m → ℤ → Prop
  | refl (i : Fin m) : NetworkWalk E δ i i 0
  | step {i j l : Fin m} {w : ℤ} :
      NetworkWalk E δ i j w → (j, l) ∈ E → NetworkWalk E δ i l (w + δ j l)

/-- Neumann, Schwindt & Zimmermann, *Project Scheduling with Time Windows and Scarce Resources*,
2nd ed., §1.1–1.2, §2.1 and §3.1 (pp. 1–8, 24–25, 197). A project of Chapter 3 with activities
`V = {0, 1, …, n+1}` (`Fin (n + 2)`, `n ≥ 1`; `0` is the project beginning, `Fin.last (n+1)` the
project completion), an AoN network with arc set `E` and integer arc weights `δ i j`, integer
durations `p i` (zero for the two fictitious activities, positive for the real activities
`1, …, n`), renewable resources `k ∈ K` with integer capacities `R k` and requirements
`r i k ≤ R k` (zero for the fictitious activities), and a prescribed maximum project duration
`d̄ ∈ ℕ`. As §3.1 prescribes, `E` contains the backward arc `⟨n+1, 0⟩` with weight
`δ_{n+1,0} = −d̄`, which encodes `S_{n+1} ≤ d̄` (3.1.1). The standing consequence of
Definition 1.1.1 and Remarks 1.1.2 stated on p. 8 is kept as a field: from every node `i` there
is a path to node `n+1` whose length is at least `p_i`. -/
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
  /-- The prescribed maximum project duration `d̄ ∈ ℕ` of (3.1.1). -/
  dbar : ℕ
  /-- There is at least one real activity (`n ≥ 1`, §1.1). -/
  one_le_n : 1 ≤ n
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
  /-- §3.1 (p. 197): the network contains the backward arc `⟨n+1, 0⟩` … -/
  back_arc : (Fin.last (n + 1), 0) ∈ E
  /-- … weighted by `δ_{n+1,0} = −d̄`, which encodes `S_{n+1} ≤ d̄`. -/
  back_weight : δ (Fin.last (n + 1)) 0 = -(dbar : ℤ)
  /-- p. 8 (from Definition 1.1.1 and Remarks 1.1.2): for each node `i` there is a path from
  `i` to node `n+1` whose length is at least `p_i`. -/
  path_to_last : ∀ i : Fin (n + 2), ∃ w : ℤ, (p i : ℤ) ≤ w ∧ NetworkWalk E δ i (Fin.last (n + 1)) w

variable {n : ℕ} {K : Type}

/-- Definition 1.3.1, Eq. (1.2.1) and problem (3.1.2) (p. 197): the set `S_T` of time-feasible
schedules, i.e. vectors `S = (S_0, …, S_{n+1})` of real start times with `S_0 = 0`, `S_i ≥ 0` and
`S_j − S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E` (the deadline `S_{n+1} ≤ d̄` is the backward
arc). -/
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

/-- Definition 2.1.1 with the resource constraints of (3.1.2) (p. 197): the set `S_R` of
resource-feasible schedules (`S_0 = 0`, `S ≥ 0`, and `r_k(S, t) ≤ R_k` for every resource `k`
and every time `t ≥ 0`). The constraint is imposed for all `t ≥ 0`; since every activity ends by
`S_{n+1} ≤ d̄` (field `path_to_last`), this is the same as `0 ≤ t ≤ d̄` in (3.1.2). -/
def resourceFeasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  {S | S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ ∀ k, ∀ t : ℝ, 0 ≤ t → usage P S k t ≤ P.R k}

/-- Problem (3.1.2) (p. 197): the feasible region `𝒮 = S_T ∩ S_R` of `PS|temp,d̄|f`. -/
def feasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  timeFeasibleSet P ∩ resourceFeasibleSet P

/-- §3.1 (p. 197): a feasible schedule `S` is optimal for `PS|temp,d̄|f` if it minimizes the
objective function `f` on the whole feasible region `𝒮`. -/
def IsOptimal (P : Project n K) (f : (Fin (n + 2) → ℝ) → ℝ) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ∀ S' ∈ feasibleSet P, f S ≤ f S'

/-- Definition 2.3.5 (p. 32): the schedule-induced strict order
`O(S) = {(i, j) ∈ V × V | i ≠ j, S_j ≥ S_i + p_i}`. -/
def scheduleOrder (P : Project n K) (S : Fin (n + 2) → ℝ) : Set (Fin (n + 2) × Fin (n + 2)) :=
  {e | e.1 ≠ e.2 ∧ S e.1 + (P.p e.1 : ℝ) ≤ S e.2}

/-- Definition 2.3.1 (p. 30; a polytope in Chapter 3, p. 198): the order polytope
`S_T(O) = {S ∈ S_T | S_j ≥ S_i + p_i for all (i, j) ∈ O}`. For `O = O(S)` it is the schedule
polytope `S_T(O(S))` of Definition 2.3.5. -/
def orderPolytope (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2))) :
    Set (Fin (n + 2) → ℝ) :=
  {S | S ∈ timeFeasibleSet P ∧ ∀ e ∈ O, S e.1 + (P.p e.1 : ℝ) ≤ S e.2}

/-- Eq. (3.3.10) (p. 227): the equal-order set of schedule `S`,
`S_T^=(O(S)) = {S' ∈ S_T(O(S)) | O(S') = O(S)}`. -/
def equalOrderSet (P : Project n K) (S : Fin (n + 2) → ℝ) : Set (Fin (n + 2) → ℝ) :=
  {S' | S' ∈ orderPolytope P (scheduleOrder P S) ∧ scheduleOrder P S' = scheduleOrder P S}

end ProjSchedTW.ObjectiveClasses


