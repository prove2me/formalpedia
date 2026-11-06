-- Prove2me | Definitions.Def_IPMJumpLB_FlowInstance
-- name    : IPMJumpLB_FlowInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:23.966226+00:00
-- url     : https://prove2.me/theorems/e00e0d7b-66f4-4a13-bbf1-006173605bf2
-- title:
--   Min-cost flow instance $(G, c, d)$ on a directed graph
-- statement:
--   A **min-cost flow instance** $(G, c, d)$ consists of a directed graph $G = (V, E)$ (the published general digraph `CombOpt.MinCostFlow.Digraph`: arc types with a tail and a head map; loops and parallel arcs allowed), arc costs $c \in \mathbb R^E$ and vertex demands $d \in \mathbb R^V$. Each arc $e \in E$ has a tail $u$ and a head $v$, written $e = (u, v)$; a positive demand $d_u$ is a supply.
--
--   The instance determines the primal-dual pair
--   $$
--   \min_f \{\langle c, f\rangle : B^\top f = d,\ f \ge 0\} = \max_x \{\langle d, x\rangle : Bx \le c\},
--   $$
--   where $B \in \mathbb R^{E \times V}$ is the arc-vertex incidence matrix. All objects of the mission (slacks, flow conservation, the duality gap, iterates and jumps) are defined over such an instance.
--
--   **Formalization Note** Vertices and arcs are arbitrary types, finite in every use, and an arc is an element of the arc type with a `tail` and a `head`. The page's condition $\sum_v d_v = 0$ is not a field: Theorem 4.1 and its proof never use it, and the instance of Section 4 satisfies it.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 2, p.3

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace IPMJumpLB

/-- A min-cost flow instance `(G, c, d)` (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §2, p.3): a directed graph `G = (V, E)` (the
published general digraph `CombOpt.MinCostFlow.Digraph`, giving the tail and the head of every
arc) together with arc costs `c ∈ ℝ^E` and vertex demands `d ∈ ℝ^V`.

**Formalization Note** Vertices and arcs are types (finite in every use); arc `e` goes from
`tail e` to `head e`. The page's standing condition `∑_v d_v = 0` is not a field: Theorem 4.1 and
its proof never use it, and the instance of Section 4 satisfies it. -/
structure FlowInstance (V E : Type*) extends CombOpt.MinCostFlow.Digraph V E where
  /-- the arc costs `c_e` -/
  cost : E → ℝ
  /-- the vertex demands `d_v` (positive = supply) -/
  demand : V → ℝ

end IPMJumpLB


