-- Prove2me | Definitions.Def_ContPatrol_MetricGraph
-- name    : ContPatrol_MetricGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:34.398982+00:00
-- url     : https://prove2.me/theorems/1698ba63-a21a-4833-9859-e5ae239c9d00
-- title:
--   Metric graph: arc lengths $\lambda(e)$ and vertex distance
-- statement:
--   A **metric graph** is a multigraph in which every edge $e$ has a length $\lambda(e)>0$. The length of a walk is the sum of the lengths of its edges, and the distance $d(u,w)$ between two vertices is the minimum length of a walk from $u$ to $w$.
--
--   This is the paper's starting point: "we begin with a graph $G$ with edges and vertices, with the addition of a length $\lambda(e)$ assigned to each edge $e$", and the metric is "the minimum length of a path between $x$ and $y$".
--
--   **Formalization Note** The vertex distance is an infimum of reals; it would be $0$ for two vertices joined by no walk, which never happens on a network (networks are connected).
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, pp.4–5

import Mathlib
import Definitions.Def_ContPatrol_Multigraph

namespace ContPatrol

/-- **A finite multigraph with positive arc lengths.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, pp.4–5:
"we begin with a graph G with edges and vertices, with the addition of a length λ(e) assigned to
each edge e."

`len e` is the length `λ(e) > 0` of edge `e`. `walkLen ds` is the total length of a walk, and
`vdist u w` the minimum length of a walk from `u` to `w` (the paper's metric `d` restricted to
vertices, p.5: "the minimum length of a path between x and y").

**Formalization Note.** `vdist` is an infimum of real numbers; when no walk joins `u` and `w` it
is `sInf ∅ = 0`. Every statement of this mission assumes the graph is connected
(`MetricGraph.IsNetwork`), so this junk value never occurs there. The minimum is attained: a
shortest walk can be taken without repeated vertices. -/
structure MetricGraph (V E : Type) extends Multigraph V E where
  /-- The length `λ(e)` of each edge. -/
  len : E → ℝ
  /-- Edge lengths are positive. -/
  len_pos : ∀ e, 0 < len e

namespace MetricGraph

variable {V E : Type}

/-- The length of a walk: the sum of the lengths of its edges. -/
def walkLen (G : MetricGraph V E) (ds : List (E × Bool)) : ℝ :=
  (ds.map fun d => G.len d.1).sum

/-- The distance between two vertices: the minimum length of a walk joining them. -/
noncomputable def vdist (G : MetricGraph V E) (u w : V) : ℝ :=
  sInf {r | ∃ ds, G.IsWalk u w ds ∧ G.walkLen ds = r}

end MetricGraph

end ContPatrol


