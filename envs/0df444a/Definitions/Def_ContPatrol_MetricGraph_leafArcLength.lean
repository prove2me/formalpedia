-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_leafArcLength
-- name    : ContPatrol_MetricGraph_leafArcLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:48.876458+00:00
-- url     : https://prove2.me/theorems/57d6acac-ba63-4774-a56e-070147342875
-- title:
--   Leaf nodes, their number $l$, and leaf-arc lengths
-- statement:
--   A **leaf node** is a vertex of degree $1$; $l$ denotes the number of leaf nodes, and the leaf nodes are also regarded as points of $Q$.
--
--   The **leaf arc** at a leaf node $v$ is its incident arc, which runs from $v$ through vertices of degree $2$ (regular points of $Q$) to the first node of degree at least $3$. Its length is the distance from $v$ to the nearest vertex of degree at least $3$.
--
--   Leaf nodes are where the Patroller's tour pauses and where the Attacker's independent attack strategy concentrates.
--
--   **Formalization Note** The leaf-arc length is not the length of the single edge at $v$ when the arc is subdivided by degree-2 vertices. It is only used at leaves of networks, where a vertex of degree at least $3$ exists because $Q$ is not a line segment.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, p.5

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_Point

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- **Leaf nodes, their number l, and the leaf points.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.5:
"A node of degree 1 is called a leaf node, and its incident arc is called a leaf arc."

`G.leaves` is the set of vertices of degree 1, `G.leafCount` their number `l`, and
`G.leafPoints` the same vertices as points of Q. -/
def leaves [Fintype V] [Fintype E] [DecidableEq V] (G : MetricGraph V E) : Finset V :=
  Finset.univ.filter fun v => G.deg v = 1

/-- The number `l` of leaf nodes. -/
def leafCount [Fintype V] [Fintype E] [DecidableEq V] (G : MetricGraph V E) : ℕ :=
  G.leaves.card

/-- The leaf nodes as points of Q. -/
def leafPoints [Fintype V] [Fintype E] [DecidableEq V] (G : MetricGraph V E) : Finset G.Point :=
  G.leaves.map ⟨Sum.inl, Sum.inl_injective⟩

/-- **The length of the leaf arc at a leaf node.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.5:
the leaf arc of a leaf node is its incident arc, the path of regular points from it to the
adjacent node.

`G.leafArcLength v` is the distance from `v` to the nearest vertex of degree at least 3.

**Formalization Note.** Vertices of degree 2 of the graph are regular points of Q, so the leaf
arc at a leaf `v` is the chain of edges from `v` through degree-2 vertices up to the first vertex
of degree at least 3 (which exists in a network with a leaf, since Q is not a line segment). Its
length is the distance from `v` to the nearest vertex of degree at least 3, which is what is
defined here; it is not the length of the single edge at `v`. The value is only used at leaves of
networks; elsewhere the infimum may be `sInf ∅ = 0`. -/
noncomputable def leafArcLength [Fintype E] [DecidableEq V] (G : MetricGraph V E) (v : V) : ℝ :=
  sInf ((fun u => G.vdist v u) '' {u | 3 ≤ G.deg u})

end MetricGraph

end ContPatrol


