-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_dist
-- name    : ContPatrol_MetricGraph_dist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:51.010475+00:00
-- url     : https://prove2.me/theorems/325abc3c-b786-4e60-b1d3-303d27eccaa9
-- title:
--   The metric $d$ on $Q$: minimum length of a path
-- statement:
--   For points $x,y$ of $Q$, $d(x,y)$ is the minimum length of a path from $x$ to $y$. Concretely it is the least of the following numbers:
--
--   1. for an end $a$ of the edge containing $x$ and an end $b$ of the edge containing $y$: the distance from $x$ to $a$ along its edge, plus the vertex distance $d(a,b)$, plus the distance from $b$ to $y$ along its edge (a vertex is its own unique end, at distance $0$);
--   2. if $x$ and $y$ lie in the same open edge at offsets $s$ and $t$: $|s-t|$.
--
--   All interception and patrol constraints of the game are expressed with this metric.
--
--   **Formalization Note** A shortest path either stays in one edge or leaves the edges of $x$ and $y$ through their ends, so the finite minimum above is the paper's metric. On a loop of length $\lambda$ it gives $\min(|s-t|,\lambda-|s-t|)$.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, p.5

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_Point

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- The vertices bounding the edge of a point, each with its distance from the point along that
edge: a vertex `v` gives `[(v, 0)]`; the point at offset `s` on edge `e` gives
`[(src e, s), (tgt e, λ(e) − s)]`. -/
def ends (G : MetricGraph V E) : G.Point → List (V × ℝ)
  | Sum.inl v => [(v, 0)]
  | Sum.inr ⟨e, s⟩ => [(G.src e, (s : ℝ)), (G.tgt e, G.len e - s)]

/-- **The metric d on Q.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.5:
"We take the metric d(x,y) on Q as the minimum length of a path between x and y."

`G.dist p q` is the least of: for each end `a` of the edge of `p` and each end `b` of the edge of
`q`, the distance from `p` to `a` along its edge plus the walk distance `vdist a b` plus the
distance from `b` to `q` along its edge; and, when `p` and `q` lie in the same open edge at offsets
`s` and `t`, the direct distance `|s − t|`.

**Formalization Note.** A shortest path between two points either stays inside one edge or leaves
the edge of each point through one of its ends, so this finite minimum is the paper's `d`. For a
loop `e` at `v` and two points at offsets `s, t` it gives `min(|s − t|, λ(e) − |s − t|)`. The
minimum is written as `sInf` of a finite nonempty set of reals bounded below by `0`. -/
noncomputable def dist (G : MetricGraph V E) (p q : G.Point) : ℝ :=
  sInf ({r | ∃ a ∈ G.ends p, ∃ b ∈ G.ends q, r = a.2 + G.vdist a.1 b.1 + b.2} ∪
    {r | ∃ (e : E) (s t : Set.Ioo (0 : ℝ) (G.len e)),
      p = Sum.inr ⟨e, s⟩ ∧ q = Sum.inr ⟨e, t⟩ ∧ r = |(s : ℝ) - t|})

end MetricGraph

end ContPatrol


