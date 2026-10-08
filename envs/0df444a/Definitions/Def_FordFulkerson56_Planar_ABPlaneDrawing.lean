-- Prove2me | Definitions.Def_FordFulkerson56_Planar_ABPlaneDrawing
-- name    : FordFulkerson56_Planar_ABPlaneDrawing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:25:34.914657+00:00
-- url     : https://prove2.me/theorems/ad7773b8-7b03-4194-94a0-94a7c2ea7c0e
-- title:
--   ab-planarity: a crossing-free plane drawing of the graph together with an extra arc ab
-- statement:
--   Let $N$ be a network with graph $G$, source $a$ and sink $b$. Ford and Fulkerson call $N$ **planar with respect to its source and sink**, or **ab-planar**, if the graph $G$ together with an additional arc $ab$ joining the source and the sink is a planar graph, i.e. can be drawn in the plane without crossings.
--
--   An **ab-plane drawing** of $N$ assigns
--
--   1. to every vertex $v$ a point $p(v)\in\mathbb R^2$, distinct vertices receiving distinct points;
--   2. to every arc $e$ of $G$, and to the additional arc $ab$, a **simple arc** in $\mathbb R^2$, i.e. an injective continuous path $\gamma_e:[0,1]\to\mathbb R^2$, running from the point of one end vertex of $e$ to the point of the other (for the arc $ab$: from $p(a)$ to $p(b)$),
--
--   such that
--
--   3. an arc passes through no vertex other than its two end vertices: if $\gamma_e(t)=p(x)$ then $x$ is an end vertex of $e$;
--   4. two distinct arcs (including the arc $ab$) meet only at endpoints of both: if $\gamma_e(s)=\gamma_{e'}(t)$ with $e\neq e'$, then $s,t\in\{0,1\}$.
--
--   $N$ is ab-planar exactly when such a drawing exists.
--
--   The added arc $ab$ is what makes ab-planarity stronger than planarity of $G$: the "gas, water, electricity" graph with one arc removed (Fig. 2 of the paper) is planar, but not ab-planar when $a,b$ are the ends of the removed arc.
--
--   **Formalization Note** The arcs of the drawing are indexed by `Option E`: `none` is the added arc $ab$, `some e` is the arc $e$ of $G$; `endA`, `endB` give their end vertices. The fields mirror the published `RobertsonSeymour1986.GM5.PlaneDrawing` (a copy of `FourColor.PlaneDrawing`), which is stated for a `SimpleGraph` and therefore cannot carry parallel arcs or the extra arc $ab$; it is not reused. Each arc is drawn once, so no reversal field is needed.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), pp. 402–403, §2, definition of ab-planar network; p. 399, §1 (arcs pass through no other vertices and meet other arcs only in vertices)

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network

namespace FordFulkerson56.Planar

variable {V E : Type*}

/-- First end vertex of an arc of the graph `G` of `N` together with the extra arc `ab`:
`none` is the added arc `ab` (end vertex the source `a`), `some e` is the arc `e` of `G`. -/
def endA (N : FordFulkerson56.MinCut.Network V E) : Option E → V
  | none => N.source
  | some e => N.tail e

/-- Second end vertex of an arc of `G` together with the extra arc `ab`:
`none` is the added arc `ab` (end vertex the sink `b`), `some e` is the arc `e` of `G`. -/
def endB (N : FordFulkerson56.MinCut.Network V E) : Option E → V
  | none => N.sink
  | some e => N.head e

/-- A drawing in the real plane, without crossings, of the graph `G` of the network `N` together with
an extra arc `ab` joining the source and the sink (Ford–Fulkerson, §2, pp. 402–403). Arcs are indexed by
`Option E`: `none` is the added arc `ab`, `some e` is the arc `e` of `G`. Vertices go to distinct
points; each arc is a simple arc (an injective path) between the points of its two end vertices; an arc
passes through no vertex other than its end vertices; two distinct arcs meet only at endpoints of both.
`N` is *ab-planar* when `Nonempty (ABPlaneDrawing N)`.

**Formalization Note** The fields mirror the published `RobertsonSeymour1986.GM5.PlaneDrawing`
(id `c5313f87-e6a8-4024-87ed-632a0a93b198`, a copy of `FourColor.PlaneDrawing`). That definition is
for a `SimpleGraph`, so it cannot carry the parallel arcs of the paper's graph nor the extra arc `ab`;
here arcs are indexed by `Option E` and each arc is drawn once (no `arc_reverse` field is needed). -/
structure ABPlaneDrawing (N : FordFulkerson56.MinCut.Network V E) where
  /-- The point representing each vertex. -/
  vertex : V → ℝ × ℝ
  vertex_injective : Function.Injective vertex
  /-- The simple arc representing each arc, from the point of `endA N e` to the point of `endB N e`. -/
  arc : (e : Option E) → Path (vertex (endA N e)) (vertex (endB N e))
  arc_injective : ∀ e, Function.Injective (arc e)
  arc_avoids_vertices : ∀ (e : Option E) (t : unitInterval) (x : V),
    arc e t = vertex x → x = endA N e ∨ x = endB N e
  arcs_meet_only_at_ends : ∀ e e' : Option E, e ≠ e' → ∀ s t : unitInterval,
    arc e s = arc e' t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)

end FordFulkerson56.Planar


