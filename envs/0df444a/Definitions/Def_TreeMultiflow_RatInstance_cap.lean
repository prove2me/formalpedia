-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_cap
-- name    : TreeMultiflow_RatInstance_cap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:44.689219+00:00
-- url     : https://prove2.me/theorems/a75e2814-d673-4450-a864-91e0c9c3c713
-- title:
--   Edge capacities of a rational instance
-- statement:
--   The capacity $u_e$ of an edge $e$ of a rational instance is the capacity listed with that edge (and $0$ for a pair that is not listed, a value that is never used).
--
--   **Formalization Note** On well-formed instances every edge is listed exactly once.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (integer capacity u_e ≥ 1 for each edge)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance_vertex

namespace TreeMultiflow

/-- **Edge capacities of a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2 ("let uₑ ≥ 1 be an integer capacity for each edge e").

`I.cap e` is the capacity listed with the first entry of `I.edges` joining the two endpoints of
`e`, and `0` when no entry does.

**Formalization Note.** On well-formed instances every edge is listed exactly once
(`RatInstance.WellFormed`), so `I.cap e` is its listed capacity; the value `0` off the edges is
never used, since feasibility constrains only edges of the graph. -/
def RatInstance.cap (I : RatInstance) (e : Sym2 (Fin (I.n + 1))) : ℕ :=
  ((I.edges.find? fun t => decide (s(I.vertex t.1, I.vertex t.2.1) = e)).map
    fun t => t.2.2).getD 0

end TreeMultiflow


