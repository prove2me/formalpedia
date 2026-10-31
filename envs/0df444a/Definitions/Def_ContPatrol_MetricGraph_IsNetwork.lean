-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_IsNetwork
-- name    : ContPatrol_MetricGraph_IsNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:26.151205+00:00
-- url     : https://prove2.me/theorems/402d23c7-bc6f-4f75-b51d-0afc0f990c02
-- title:
--   Network $Q$: connected, at least one arc, not a line segment
-- statement:
--   A metric graph is a **network** if
--
--   1. it has at least one edge,
--   2. it is connected, and
--   3. it is not a line segment: some vertex has degree at least $3$, or no vertex has degree $1$.
--
--   The paper takes $Q$ connected and excludes the line segment network "to ensure that every leaf arc has a single leaf node in its closure".
--
--   **Formalization Note** In a connected multigraph, "every degree is at most $2$ and some degree is $1$" holds exactly for a path, i.e. a subdivided segment. Vertices of degree $2$ are allowed: they are regular points of $Q$, not nodes, and the circle is a single loop at a vertex of degree $2$. The graph is finite, as in the paper.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, pp.4–5

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- **Network.** Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*,
arXiv:2008.07369v2, §3, pp.4–5: Q is a connected network built from a graph with positive edge
lengths, and "To ensure that every leaf arc has a single leaf node in its closure, we exclude the
line segment network from consideration."

A metric graph is a *network* if it has at least one edge, is connected, and is not a line
segment.

**Formalization Note.** In a connected multigraph, "every vertex has degree at most 2 and some
vertex has degree 1" holds exactly for a path, i.e. a subdivided line segment; so "not a line
segment" is `(∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1)`. Vertices of degree 2 are allowed (they are
regular points of Q, not nodes): the circle is one loop at a vertex of degree 2. Connectivity with
at least one edge excludes isolated vertices. Finiteness of `V` and `E` is the paper's (the proof
of Lemma 3, p.32: "there are a finite number of arcs"). -/
def IsNetwork [Fintype E] [DecidableEq V] (G : MetricGraph V E) : Prop :=
  Nonempty E ∧ G.Connected ∧ ((∃ v, 3 ≤ G.deg v) ∨ ∀ v, G.deg v ≠ 1)

end MetricGraph

end ContPatrol


