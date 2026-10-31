-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_AlphaLeGirth
-- name    : ContPatrol_MetricGraph_AlphaLeGirth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:31.713633+00:00
-- url     : https://prove2.me/theorems/252df464-463e-47fb-88c5-aad4e9872660
-- title:
--   Circuits and the condition $\alpha\le g$ on the girth
-- statement:
--   A **circuit** is a closed path consisting of distinct adjacent arcs: a closed dart walk whose darts use pairwise distinct edges. Its length is the sum of the lengths of its edges. The **girth** $g$ of $Q$ is the minimum length of a circuit, and $g=\infty$ if $Q$ has no circuits.
--
--   The condition $\alpha\le g$ says that every circuit has length at least $\alpha$.
--
--   **Formalization Note** The girth itself is not materialized; the condition $\alpha\le g$ is stated directly, which is exact also when there is no circuit.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, p.5; §4, p.11

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- **Circuits.** Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*,
arXiv:2008.07369v2, §3, p.5: "A circuit in Q is a closed path (that is, with the same startpoint
and endpoint) consisting of distinct adjacent arcs."

A circuit is a closed dart walk whose darts use pairwise distinct edges; a loop is a circuit of
one edge, and two parallel edges form a circuit of two. Its length is `G.walkLen w`.

**Formalization Note.** Arcs of Q are chains of edges through degree-2 vertices; a closed walk
with distinct edges through a degree-2 vertex must leave by the other edge, so circuits of Q and
of the graph are the same closed curves with the same lengths. -/
def IsCircuit (G : MetricGraph V E) (w : List (E × Bool)) : Prop :=
  G.IsClosedDartWalk w ∧ (w.map Prod.fst).Nodup

/-- **α ≤ g, the girth.** Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*,
arXiv:2008.07369v2, §4, p.11: "the girth g of Q, defined for networks as the minimum length of a
circuit in Q, and if Q has no circuits then g = ∞."

`G.AlphaLeGirth α` says `α ≤ g`: every circuit has length at least `α`.

**Formalization Note.** The girth itself (possibly `∞`) is not materialized; the condition
`α ≤ g` is stated directly, which is exact also when there is no circuit (`g = ∞`). -/
def AlphaLeGirth (G : MetricGraph V E) (α : ℝ) : Prop :=
  ∀ w, G.IsCircuit w → α ≤ G.walkLen w

end MetricGraph

end ContPatrol


