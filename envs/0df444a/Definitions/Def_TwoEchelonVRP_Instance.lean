-- Prove2me | Definitions.Def_TwoEchelonVRP_Instance
-- name    : TwoEchelonVRP_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:25:13.032667+00:00
-- url     : https://prove2.me/theorems/1b31017f-752a-4716-9fc6-ee91334028a1
-- title:
--   Instance of the two-echelon capacitated vehicle routing problem (2E-CVRP)
-- statement:
--   The 2E-CVRP is posed on an undirected graph $G = (N, E)$ whose vertex set is partitioned as
--
--   $$
--   N = \{0\} \cup N_S \cup N_C ,
--   $$
--
--   where vertex $0$ is the **depot**, $N_S = \{1, \dots, n_s\}$ are the $n_s$ **satellites** and $N_C = \{n_s+1, \dots, n_s+n_c\}$ are the $n_c$ **customers**. This file also defines the edge set
--
--   $$
--   E = \{\{0, j\} : j \in N_S\} \cup \{\{i, j\} : i, j \in N_S \cup N_C,\ i < j\},
--   $$
--
--   so the depot is adjacent to every satellite and to no customer, and any two distinct satellites or customers are adjacent. It also defines an **instance** of the 2E-CVRP: travel costs $d_{ij}$ on the edges, symmetric and satisfying the triangle inequality on every triangle of $G$; customer demands $q_i$ (units of goods); $m^1$ first-level vehicles of capacity $Q_1$ and fixed cost $U_1$ at the depot; for each satellite $k$ a capacity $B_k$, $m_k$ second-level vehicles of capacity $Q_2 < Q_1$ and a handling cost $H_k$ per unit delivered; a global bound $m^2 \le \sum_{k \in N_S} m_k$ on the second-level vehicles used, each with fixed cost $U_2$; and the total demand $q_{\mathrm{tot}} = \sum_{i \in N_C} q_i$.
--
--   These are the data of every formulation of the paper (F, its LP relaxation LF and the Lagrangean relaxation RF).
--
--   **Formalization Note** Vertices are `Option (Fin ns ⊕ Fin nc)` with `none` the depot, 0-based indices. `d` is a function on all ordered pairs; only its values on edges enter the model, and symmetry and the triangle inequality are imposed on edges and triangles of $G$ only. Because the non-depot vertices are pairwise adjacent and the depot is adjacent to every satellite, the triangle inequality on triangles implies $d_{uw} \le$ the cost of any $u$–$w$ path. Demands, capacities $Q_1, Q_2$ and vehicle numbers are natural numbers (goods are counted in units and deliveries are integers, constraint (11)); $B_k$, $H_k$, $U_1$, $U_2$ and $d$ are real with no sign assumed. The vehicle-count field $m_k$ is named `mSat`. The module declares `Vertex`, `IsEdge`, `Instance` and `qtot`.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2, unnumbered, p. 299 (problem description: graph G = (N, E), edge set E, triangle inequality, demands q_i, q_tot, fleets m^1, Q_1, U_1, B_k, m_k, Q_2 < Q_1, m^2 ≤ Σ m_k, U_2, H_k)

import Mathlib

namespace TwoEchelonVRP

/-- **Vertices of the 2E-CVRP graph.**
Baldacci, Mingozzi, Roberti & Wolfler Calvo, *An Exact Algorithm for the Two-Echelon Capacitated
Vehicle Routing Problem*, Operations Research 61(2) (2013) 298–314, §2, unnumbered, p. 299:
"the vertex set N is partitioned as N = {0} ∪ N_S ∪ N_C. Vertex 0 represents the depot,
N_S = {1, 2, …, n_s} represents n_s satellites, and N_C = {n_s + 1, …, n_s + n_c} represents n_c
customers."

**Formalization Note.** `none` is the depot 0, `some (Sum.inl k)` is satellite `k : Fin ns` and
`some (Sum.inr i)` is customer `i : Fin nc` (0-based indices; the paper's satellite `k` is
`k - 1` and its customer `n_s + i` is `i - 1`). -/
abbrev Vertex (ns nc : ℕ) : Type := Option (Fin ns ⊕ Fin nc)

/-- **Edges of the 2E-CVRP graph.**
Baldacci et al., Operations Research 61(2) (2013), §2, unnumbered, p. 299: "The edge set E is
defined as E = {{0, j} : j ∈ N_S} ∪ {{i, j} : i, j ∈ N_S ∪ N_C, i < j}."

`IsEdge u v` holds when `{u, v} ∈ E`: one endpoint is the depot and the other a satellite, or both
endpoints are distinct non-depot vertices (satellites or customers). The depot is adjacent to no
customer.

**Formalization Note.** `E` is a set of unordered pairs; `IsEdge` is the symmetric relation
`{u, v} ∈ E` on ordered pairs. -/
def IsEdge {ns nc : ℕ} : Vertex ns nc → Vertex ns nc → Prop
  | none, some (Sum.inl _) => True
  | some (Sum.inl _), none => True
  | some a, some b => a ≠ b
  | _, _ => False

/-- **An instance of the two-echelon capacitated vehicle routing problem (2E-CVRP).**
Baldacci et al., Operations Research 61(2) (2013), §2, unnumbered, p. 299.

* `d u v` is the travel cost `d_ij` of edge `{u, v} ∈ E`; G is undirected, so `d` is symmetric on
  edges. "We assume that matrix d_ij satisfies the triangle inequality" (field `triangle`).
* `q i` is the demand of customer `i` ("Each customer i ∈ N_C requires q_i units of goods").
* `m1` vehicles of capacity `Q1` serve the satellites from the depot, each with fixed cost `U1`.
* Satellite `k` has capacity `B k` (total demand delivered to it), `mSat k` (the paper's `m_k`) vehicles of capacity
  `Q2 < Q1`, and handling cost `H k` per unit delivered to it. "at most m² ≤ Σ_{k∈N_S} m_k
  second-level vehicles can be globally used" (fields `m2`, `m2_le`); a second-level vehicle has
  fixed cost `U2`.

**Formalization Note.**
1. `d` is a function on all ordered pairs of vertices; only its values on edges of `G` enter the
   model. Symmetry and the triangle inequality are imposed on edges and triangles of `G` only
   (the paper's `d` is defined only on `E`). Since every two non-depot vertices are adjacent and
   the depot is adjacent to every satellite, the triangle inequality on triangles of `G` implies
   `d_uw ≤` the cost of any path from `u` to `w` in `G`.
2. Demands, vehicle numbers and capacities are natural numbers: goods are counted in units, and
   the quantities `q_kr` shipped by first-level routes are nonnegative integers (constraint (11)).
   `B`, `H`, `U1`, `U2` and `d` are real; no sign is assumed, as the paper assumes none. -/
structure Instance (ns nc : ℕ) where
  /-- travel cost `d_ij` -/
  d : Vertex ns nc → Vertex ns nc → ℝ
  /-- `G` is undirected -/
  d_symm : ∀ u v, IsEdge u v → d u v = d v u
  /-- triangle inequality on the triangles of `G` -/
  triangle : ∀ u v w, IsEdge u v → IsEdge v w → IsEdge u w → d u w ≤ d u v + d v w
  /-- customer demands `q_i` -/
  q : Fin nc → ℕ
  /-- number `m¹` of first-level vehicles -/
  m1 : ℕ
  /-- capacity `Q_1` of a first-level vehicle -/
  Q1 : ℕ
  /-- fixed cost `U_1` of a first-level vehicle -/
  U1 : ℝ
  /-- satellite capacities `B_k` -/
  B : Fin ns → ℝ
  /-- number `m_k` of second-level vehicles at satellite `k` (field `mSat`) -/
  mSat : Fin ns → ℕ
  /-- capacity `Q_2` of a second-level vehicle -/
  Q2 : ℕ
  /-- `Q_2 < Q_1` -/
  Q2_lt_Q1 : Q2 < Q1
  /-- global bound `m²` on the number of second-level vehicles -/
  m2 : ℕ
  /-- `m² ≤ Σ_{k ∈ N_S} m_k` -/
  m2_le : m2 ≤ ∑ k, mSat k
  /-- fixed cost `U_2` of a second-level vehicle -/
  U2 : ℝ
  /-- handling cost `H_k` per unit delivered to satellite `k` -/
  H : Fin ns → ℝ

/-- **Total demand** `q_tot = Σ_{i ∈ N_C} q_i`.
Baldacci et al., Operations Research 61(2) (2013), §2, unnumbered, p. 299. -/
def qtot {ns nc : ℕ} (I : Instance ns nc) : ℕ := ∑ i, I.q i

end TwoEchelonVRP


