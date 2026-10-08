-- Prove2me | Definitions.Def_ProjSchedTW_StableSchedules_Project
-- name    : ProjSchedTW_StableSchedules_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T00:31:01.181256+00:00
-- url     : https://prove2.me/theorems/1a9b2832-9302-4046-9670-af3cfaf57248
-- title:
--   §3.1 — project network with deadline arc, renewable resources, feasible region, schedule-induced orders and order polytopes
-- statement:
--   This file fixes the project model of Chapter 3 of Neumann, Schwindt and Zimmermann.
--
--   A **project** consists of activities $V=\{0,1,\dots,n+1\}$ with $n\ge 1$, where $0$ is the project beginning and $n+1$ the project completion. Activity $i$ has an integer duration $p_i$, with $p_0=p_{n+1}=0$ and $p_i>0$ for the real activities $i=1,\dots,n$. The **project network** $N$ has node set $V$, a loop-free arc set $E$ and integer arc weights $\delta_{ij}$ (minimum and maximum time lags). There is a finite set $\mathcal R$ of renewable resources; resource $k$ has capacity $R_k\in\mathbb N$, and activity $i$ needs $r_{ik}\in\mathbb Z_{\ge 0}$ units of it, where $r_{ik}\le R_k$ and $r_{0k}=r_{n+1,k}=0$. A prescribed maximum project duration $\bar d\in\mathbb N$ is part of the network, as in Chapter 3: $E$ contains the backward arc $\langle n+1,0\rangle$ with weight $\delta_{n+1,0}=-\bar d$.
--
--   A **schedule** is a vector $S=(S_i)_{i\in V}\in\mathbb R^{n+2}$ of start times. The objects defined here are:
--
--   1. the **time-feasible region**
--   $$\mathcal S_T=\{S\in\mathbb R^{n+2}\mid S_0=0,\ S_i\ge 0\ (i\in V),\ S_j-S_i\ge\delta_{ij}\ (\langle i,j\rangle\in E)\};$$
--   because of the backward arc it contains the deadline $S_{n+1}\le\bar d$ of (3.1.1);
--   2. the **active set** $\mathcal A(S,t)=\{i\in V\mid S_i\le t<S_i+p_i\}$ and the **resource usage** $r_k(S,t)=\sum_{i\in\mathcal A(S,t)}r_{ik}$;
--   3. the **resource-feasible** schedules $\mathcal S_R$ (those with $S_0=0$, $S\ge 0$ and $r_k(S,t)\le R_k$ for all $k\in\mathcal R$ and $t\ge 0$), and the **feasible region** $\mathcal S=\mathcal S_T\cap\mathcal S_R$ of problem (3.1.2);
--   4. the **schedule-induced strict order** $O(S)=\{(i,j)\in V\times V\mid i\ne j,\ S_j\ge S_i+p_i\}$;
--   5. **strict orders** in $V$ (asymmetric and transitive relations), the **order polytope** $\mathcal S_T(O)=\{S\in\mathcal S_T\mid S_j\ge S_i+p_i\ \text{for all}\ (i,j)\in O\}$ (the **schedule polytope** when $O=O(S)$), and **feasible** strict orders: those with $\mathcal S_T(O)\neq\emptyset$ and $\mathcal S_T(O)\subseteq\mathcal S$.
--
--   These are the objects on which every statement of §3.2 is phrased.
--
--   **Formalization Note** Activities are `Fin (n + 2)`, with `0` the project beginning and `Fin.last (n+1)` the project completion. Start times are real. The resource constraints are imposed for every $t\ge 0$ rather than for $0\le t\le\bar d$ as (3.1.2) writes; the book's proofs use the $t\ge 0$ reading. The deadline is stored as the field `dbar` together with the arc $\langle n+1,0\rangle\in E$ of weight $-\bar d$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 24–25 (Eqs. (2.1.1), (2.1.2), Definition 2.1.1), pp. 30–32 (Definitions 2.3.1, 2.3.5), p. 197 (Eq. (3.1.1), problem (3.1.2)), p. 198 (polytopes)

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project

namespace ProjSchedTW.StableSchedules

/-- Neumann, Schwindt & Zimmermann, *Project Scheduling with Time Windows and Scarce Resources*,
2nd ed., §1.1–1.2, §2.1 and §3.1 (pp. 1–7, 24–25, 197). A project of Chapter 3 with activities
`V = {0, 1, …, n+1}` (`Fin (n + 2)`, `n ≥ 1`; `0` is the project beginning, `Fin.last (n+1)` the
project completion), an AoN network with arc set `E` and integer arc weights `δ i j`, integer
durations `p i` (zero for the two fictitious activities, positive for the real activities
`1, …, n`), renewable resources `k ∈ K` with integer capacities `R k` and requirements
`r i k ≤ R k` (zero for the fictitious activities), and a prescribed maximum project duration
`d̄ ∈ ℕ`. As §3.1 prescribes, the deadline `S_{n+1} ≤ d̄` (3.1.1) is part of the network: `E`
contains the backward arc `⟨n+1, 0⟩` with weight `δ_{n+1,0} = −d̄`. -/
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

variable {n : ℕ} {K : Type}

/-- Definition 1.3.1 and Eq. (1.2.1), with (3.1.1) through the backward arc: the set `S_T` of
time-feasible schedules, i.e. vectors `S = (S_0, …, S_{n+1})` of real start times with
`S_0 = 0`, `S_i ≥ 0` and `S_j − S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E` (problem (3.1.2),
p. 197). -/
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
and every time `t ≥ 0`). The constraint is imposed for all `t ≥ 0` rather than only for
`0 ≤ t ≤ d̄` as (3.1.2) writes. -/
def resourceFeasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  {S | S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ ∀ k, ∀ t : ℝ, 0 ≤ t → usage P S k t ≤ P.R k}

/-- Definition 2.1.1 and problem (3.1.2) (p. 197): the feasible region `𝒮 = S_T ∩ S_R`. -/
def feasibleSet (P : Project n K) : Set (Fin (n + 2) → ℝ) :=
  timeFeasibleSet P ∩ resourceFeasibleSet P

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

/-- Definition 2.3.1 (p. 30): a strict order `O` is feasible if it is time-feasible
(`S_T(O) ≠ ∅`) and `S_T(O) ⊆ 𝒮`. -/
def IsFeasibleOrder (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2))) : Prop :=
  ProjSchedTW.ActiveSchedules.IsStrictOrderRel O ∧ (orderPolytope P O).Nonempty ∧ orderPolytope P O ⊆ feasibleSet P

end ProjSchedTW.StableSchedules


