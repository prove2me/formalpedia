-- Prove2me | Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
-- name    : ProjSchedTW_OrderPolyhedra_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:53:11.09563+00:00
-- url     : https://prove2.me/theorems/15158df8-ee97-41c6-bea2-7e66c63d2374
-- title:
--   §1.1–1.3 and §2.1 — project network with time lags, renewable resources, schedules and paths
-- statement:
--   This file fixes the model of a project with minimum and maximum time lags and renewable resources, following §1.1–1.3 and §2.1 of Neumann, Schwindt & Zimmermann.
--
--   The activity set is $V = \{0, 1, \dots, n+1\}$: activities $1, \dots, n$ are the real activities, $0$ is the fictitious project beginning and $n+1$ the fictitious project completion. A **project** consists of
--
--   1. durations $p_i \in \mathbb{Z}_{\ge 0}$ for $i \in V$;
--   2. the arc set $E \subseteq V \times V$ of the activity-on-node (AoN) project network $N$, with an integer weight $\delta_{ij}$ on each arc $\langle i, j\rangle \in E$ (a minimum time lag gives a nonnegative weight, a maximum time lag a nonpositive one);
--   3. a set $\mathcal R$ of renewable resources with capacities $R_k \in \mathbb{N}$ and requirements $r_{ik} \in \mathbb{Z}_{\ge 0}$.
--
--   An arc-weighted network on $V$ is an arc set together with arc weights. A **path** from $i$ to $j$ is a sequence of nodes $i = v_0, v_1, \dots, v_m = j$ with every $\langle v_{l-1}, v_l\rangle$ an arc; its **length** is $\sum_{l=1}^m w_{v_{l-1} v_l}$, and the one-node sequence is the path of length $0$ from $i$ to itself. A **cycle of positive length** is a closed path with at least one arc and positive length.
--
--   The book's **standing assumptions** on a project are collected in one predicate:
--
--   1. $n \ge 1$;
--   2. $p_0 = p_{n+1} = 0$ and $p_i > 0$ for $i = 1, \dots, n$;
--   3. $N$ has no loops;
--   4. $r_{0k} = r_{n+1,k} = 0$ and $r_{ik} \le R_k$ for all $i \in V$, $k \in \mathcal R$;
--   5. for every node $i$, $N$ contains a path from $0$ to $i$ of nonnegative length and a path from $i$ to $n+1$ of length at least $p_i$ (p. 8, a consequence of Definition 1.1.1 and Remarks 1.1.2).
--
--   A **schedule** is a vector $S = (S_0, \dots, S_{n+1})$ of real start times with $S_i \ge 0$ for all $i$ and $S_0 = 0$ (Definition 1.3.1). It is **time-feasible** if it satisfies the temporal constraints
--   $$S_j - S_i \ge \delta_{ij} \qquad (\langle i, j\rangle \in E). \tag{1.2.1}$$
--   The set of time-feasible schedules is $\mathcal S_T$.
--
--   These are the objects every statement of §2.3 is about.
--
--   **Formalization Note** $V$ is `Fin (n + 2)` with `0` the project beginning and `Fin.last (n + 1)` the project completion. Start times are real; durations and requirements are natural numbers; arc weights are integers. Paths are walks: nodes may repeat. In a network without cycles of positive length, "there is a path from $i$ to $j$ of length $\ge \ell$" is the same whether paths are required to be simple or not.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 1–2 (§1.1, Definition 1.1.1, Remarks 1.1.2), p. 8 (paths and their lengths), p. 10 (Definition 1.3.1, Eq. (1.2.1)), p. 24 (§2.1)

import Mathlib

namespace ProjSchedTW.OrderPolyhedra

/-- A project with `n` real activities, minimum and maximum time lags, and renewable resources
(Neumann–Schwindt–Zimmermann, §1.1–1.2 and §2.1, pp. 1–8 and 24–25).
The activity set is `V = {0, 1, …, n+1}`, encoded as `Fin (n + 2)`: node `0` is the project
beginning and node `Fin.last (n + 1)` the project completion.
* `p i` is the duration of activity `i`;
* `E` is the arc set of the AoN project network `N`, and `δ i j` the (integer) weight of the arc
  `⟨i, j⟩ ∈ E`; the temporal constraint of the arc is `S_j - S_i ≥ δ_ij` (Eq. (1.2.1));
* `K` is the set `ℛ` of renewable resources, `R k` the capacity of resource `k` and `r i k` the
  amount of resource `k` used by activity `i` while it is in progress. -/
structure Project (n : ℕ) (K : Type) where
  p : Fin (n + 2) → ℕ
  E : Finset (Fin (n + 2) × Fin (n + 2))
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  r : Fin (n + 2) → K → ℕ
  R : K → ℕ

/-- An arc-weighted directed network on the node set `Fin (n + 2)`: `arcs` is its arc set and
`wt i j` the weight of the arc `⟨i, j⟩` (only read for arcs in `arcs`). -/
structure Network (n : ℕ) where
  arcs : Set (Fin (n + 2) × Fin (n + 2))
  wt : Fin (n + 2) → Fin (n + 2) → ℤ

/-- The length of a sequence of nodes `v₀ v₁ … v_m` in a network: the sum of the arc weights
`wt v₀ v₁ + wt v₁ v₂ + ⋯ + wt v_{m-1} v_m` (zero for a sequence of at most one node). -/
def Network.walkLength {n : ℕ} (N : Network n) : List (Fin (n + 2)) → ℤ
  | a :: b :: l => N.wt a b + N.walkLength (b :: l)
  | _ => 0

/-- `l` is a directed path (walk) in `N` from node `i` to node `j`: a nonempty sequence of nodes
starting at `i`, ending at `j`, each consecutive pair of which is an arc of `N`. Nodes may repeat;
the one-node sequence `[i]` is the path of length `0` from `i` to itself. -/
def Network.IsPath {n : ℕ} (N : Network n) (i j : Fin (n + 2)) (l : List (Fin (n + 2))) : Prop :=
  l.head? = some i ∧ l.getLast? = some j ∧ l.IsChain (fun a b => (a, b) ∈ N.arcs)

/-- `N` contains a path from `i` to `j` whose length is at least `ℓ`. -/
def Network.HasPathOfLengthAtLeast {n : ℕ} (N : Network n) (i j : Fin (n + 2)) (ℓ : ℤ) : Prop :=
  ∃ l : List (Fin (n + 2)), N.IsPath i j l ∧ ℓ ≤ N.walkLength l

/-- `N` contains a cycle of positive length: a closed directed path (at least one arc, first node
equal to last node) whose length is positive. -/
def Network.HasPositiveCycle {n : ℕ} (N : Network n) : Prop :=
  ∃ (i : Fin (n + 2)) (l : List (Fin (n + 2))), 2 ≤ l.length ∧ N.IsPath i i l ∧ 0 < N.walkLength l

/-- The project network `N` of a project: arc set `E` with arc weights `δ`. -/
def Project.network {n : ℕ} {K : Type} (P : Project n K) : Network n :=
  ⟨↑P.E, P.δ⟩

/-- The standing assumptions of the book on a project (§1.1, p. 1 "n ≥ 1"; Remarks 1.1.2 and
p. 8; §2.1, p. 24):
1. there is at least one real activity (`n ≥ 1`);
2. the fictitious activities `0` and `n+1` have duration `0`, every real activity `1, …, n` has
   positive duration;
3. the project network has no loops;
4. `r_{0k} = r_{n+1,k} = 0` and `r_ik ≤ R_k` for all activities `i` and resources `k`;
5. for every node `i` the project network contains a path from `0` to `i` of nonnegative length
   and a path from `i` to `n+1` whose length is at least `p_i` (p. 8, consequence of
   Definition 1.1.1 and Remarks 1.1.2). -/
def Project.StandingAssumptions {n : ℕ} {K : Type} (P : Project n K) : Prop :=
  1 ≤ n ∧
  P.p 0 = 0 ∧ P.p (Fin.last (n + 1)) = 0 ∧
  (∀ i : Fin (n + 2), i ≠ 0 → i ≠ Fin.last (n + 1) → 0 < P.p i) ∧
  (∀ e ∈ P.E, e.1 ≠ e.2) ∧
  (∀ k : K, P.r 0 k = 0 ∧ P.r (Fin.last (n + 1)) k = 0) ∧
  (∀ (i : Fin (n + 2)) (k : K), P.r i k ≤ P.R k) ∧
  (∀ i : Fin (n + 2), P.network.HasPathOfLengthAtLeast 0 i 0) ∧
  (∀ i : Fin (n + 2), P.network.HasPathOfLengthAtLeast i (Fin.last (n + 1)) (P.p i))

/-- A schedule (Definition 1.3.1, p. 10): real start times `S_i ≥ 0` for all activities, with
`S_0 = 0`. -/
def IsSchedule {n : ℕ} (S : Fin (n + 2) → ℝ) : Prop :=
  S 0 = 0 ∧ ∀ i, 0 ≤ S i

/-- A time-feasible schedule (Definition 1.3.1, p. 10): a schedule satisfying the temporal
constraints `S_j - S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E` (Eq. (1.2.1)). The set `S_T`. -/
def Project.IsTimeFeasible {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  IsSchedule S ∧ ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1

end ProjSchedTW.OrderPolyhedra


