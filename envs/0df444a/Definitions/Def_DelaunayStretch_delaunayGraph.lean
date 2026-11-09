-- Prove2me | Definitions.Def_DelaunayStretch_delaunayGraph
-- name    : DelaunayStretch_delaunayGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:44.526405+00:00
-- url     : https://prove2.me/theorems/0f3d4e46-fb9e-4ab3-9d23-38a047f0a9fb
-- title:
--   The edge graph of a triangulation and Euclidean walk length
-- statement:
--   For a set $D$ of triangles in the plane, the **edge graph** joins two distinct points when some triangle of $D$ has both as vertices, that is, when they are the ends of an edge of $D$. The **length** of a walk in this graph is the sum of the Euclidean lengths $\|p-q\|$ of its edges. The shortest-path distance $d_D(u,v)$ along the edges of $D$ is the least length of a walk from $u$ to $v$.
--
--   These are the quantities in which the stretch factor $\max_{u\ne v}d_D(u,v)/\|u-v\|$ is measured.
--
--   **Formalization Note** The graph is a simple graph on $\mathbb C$; points not in any triangle are isolated.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), §1, p.3

import Mathlib

namespace DelaunayStretch

/-- The **edge graph** of a set `D` of triangles in `ℂ`: two distinct points are adjacent when
some triangle of `D` has both as vertices, i.e. when they are the ends of an edge of `D`
(§1, p.3).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), §1, p.3.

**Formalization Note** Triangles are `Finset`s of their vertices (see
`IsDelaunayTriangulation`); the edges of a triangle are the segments between two of its
vertices. -/
def delaunayGraph (D : Finset (Finset ℂ)) : SimpleGraph ℂ :=
  SimpleGraph.fromRel fun p q => ∃ T ∈ D, p ∈ T ∧ q ∈ T

/-- The Euclidean length of a walk in a graph on `ℂ`: the sum of `‖p − q‖` over its edges
`pq`. The length `d_D(u, v)` of a shortest path from `u` to `v` along the edges of `D` is the
least length of a walk from `u` to `v` in `delaunayGraph D` (§1, p.3). -/
noncomputable def walkLength {G : SimpleGraph ℂ} {u v : ℂ} (w : G.Walk u v) : ℝ :=
  (w.darts.map fun d => dist d.fst d.snd).sum

end DelaunayStretch


