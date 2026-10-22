-- Prove2me | Definitions.Def_BudgetedPCTSP_Rooted_Instance
-- name    : BudgetedPCTSP_Rooted_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:01:34.369977+00:00
-- url     : https://prove2.me/theorems/734c21ef-edac-4023-92b1-3f07a5ddbe37
-- title:
--   Instance of the rooted budgeted prize-collecting TSP: graph, edge costs, budget, root; feasible tours
-- statement:
--   An **instance** of the rooted budgeted prize-collecting traveling salesman problem (unit prizes) consists of an undirected graph $G = (V, E)$ on a finite vertex set $V$, which need not be complete, edge costs $c_e \ge 0$ for all $e \in E$, a budget $D \ge 0$, and a root $r \in V$.
--
--   The **cost** of a walk in $G$ is the sum of the costs of the edges it traverses, each edge counted as many times as it is traversed. A **feasible tour** is a closed walk $p$ in $G$ that starts and ends at the root $r$ and has cost at most $D$:
--   $$\sum_{e \in p} c_e \le D .$$
--   The tour may visit vertices more than once; the set of vertices it visits is its support. The goal of the problem is a feasible tour visiting as many vertices as possible.
--
--   **Formalization Note.** The paper defines a feasible tour as a multiset of edges $F$ that is a tour on a vertex set $S$ (a connected multigraph with all degrees even) of cost at most $D$, with $r \in S$ in the rooted version. Such a multiset is exactly the edge multiset of a closed walk at $r$ with support $S$ (Euler), so tours are represented as `SimpleGraph.Walk`s from `r` to `r` and the visited set is `p.support.toFinset`. Edge costs are a function on unordered pairs `Sym2 V`; only their values on edges of $G$ are used, and nonnegativity is required on edges only.
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript p. 1 (Section 1) and p. 3 (Section 2)

import Mathlib

namespace BudgetedPCTSP.Rooted

/-- An instance of the rooted budgeted prize-collecting traveling salesman problem with unit
prizes (Paul, Freund, Ferber, Shmoys & Williamson, Math. Oper. Res. 2020, author manuscript
p. 1 and p. 3): an undirected graph `G = (V, E)` on a finite vertex set, which need not be
complete, edge costs `c e ≥ 0` for every edge `e ∈ E`, a budget `D ≥ 0` and a root `r ∈ V`.
Edges are unordered pairs `Sym2 V`; the value of `c` on a pair that is not an edge of `G` is
never used. -/
structure Instance (V : Type) [Fintype V] [DecidableEq V] where
  /-- The undirected graph `G = (V, E)`. -/
  G : SimpleGraph V
  /-- The edge costs `c_e`. -/
  c : Sym2 V → ℝ
  /-- `c_e ≥ 0` for all `e ∈ E` (p. 1). -/
  c_nonneg : ∀ e ∈ G.edgeSet, 0 ≤ c e
  /-- The budget `D`. -/
  D : ℝ
  /-- `D ≥ 0` (p. 1). -/
  D_nonneg : 0 ≤ D
  /-- The root `r`, which the tour must contain (p. 2, p. 3). -/
  r : V

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The cost of a walk: the sum of the costs of its edges, each counted as often as the walk
traverses it (a tour is a multiset of edges, p. 1). -/
noncomputable def Instance.walkCost (I : Instance V) {u v : V} (p : I.G.Walk u v) : ℝ :=
  (p.edges.map I.c).sum

/-- A feasible tour of the rooted problem (p. 1): a closed walk `p` at the root `r` whose cost is
at most the budget `D`. Vertices may be visited more than once; the set of vertices the tour
visits is `p.support.toFinset`. The edge multiset of such a closed walk is exactly a tour in the
paper's sense (a connected multigraph with all degrees even) on a vertex set containing `r`. -/
def Instance.IsFeasibleTour (I : Instance V) (p : I.G.Walk I.r I.r) : Prop :=
  I.walkCost p ≤ I.D

end BudgetedPCTSP.Rooted


