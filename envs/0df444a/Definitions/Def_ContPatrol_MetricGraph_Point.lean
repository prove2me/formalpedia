-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_Point
-- name    : ContPatrol_MetricGraph_Point
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:29.393858+00:00
-- url     : https://prove2.me/theorems/46d61c6e-f383-4c7c-b787-44b6efdbbf8f
-- title:
--   Points of the network $Q$
-- statement:
--   Each edge $e$ of length $\lambda(e)$ is identified with an open interval $(0,\lambda(e))$, and $Q$ is the union of the vertices and these open intervals. A point of $Q$ is therefore either a vertex, or a pair $(e,s)$ with $0<s<\lambda(e)$: the point of edge $e$ at distance $s$ from $\mathrm{src}(e)$ along $e$.
--
--   The measurable sets of $Q$ are those whose trace on each open edge is a Borel set (every set of vertices is measurable).
--
--   **Formalization Note** These are the Borel sets of the metric $d$ of $Q$: $Q$ is a finite union of points and open intervals, each carrying its usual topology.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, p.4

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- **The points of the network Q.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.4:
"We can then identify an edge e with an open interval of length λ(e) ... The topology on these
intervals gives a topology on their union Q."

A point of Q is either a vertex `Sum.inl v`, or a point `Sum.inr ⟨e, s⟩` in the interior of edge
`e`, at distance `s ∈ (0, λ(e))` from `src e` along `e`.

**Formalization Note.** The measurable structure is the disjoint-union one: every set of vertices
is measurable, and on each open edge the Borel sets of the interval `(0, λ(e))`. These are the
Borel sets of the metric `d` (a finite union of closed points and open intervals). -/
def Point (G : MetricGraph V E) : Type := V ⊕ (Σ e : E, Set.Ioo (0 : ℝ) (G.len e))

/-- The measurable structure on the points of Q: discrete on vertices, Borel on each open edge. -/
instance instMeasurableSpacePoint (G : MetricGraph V E) : MeasurableSpace G.Point :=
  @Sum.instMeasurableSpace V (Σ e : E, Set.Ioo (0 : ℝ) (G.len e)) ⊤ inferInstance

end MetricGraph

end ContPatrol


