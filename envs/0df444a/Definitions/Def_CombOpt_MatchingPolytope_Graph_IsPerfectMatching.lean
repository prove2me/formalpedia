-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_IsPerfectMatching
-- name    : CombOpt_MatchingPolytope_Graph_IsPerfectMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:14.825591+00:00
-- url     : https://prove2.me/theorems/5101a0e2-9fb5-43cf-9f01-ed04fdc9fbcb
-- title:
--   A perfect matching of a graph
-- statement:
--   A matching $M$ of $G=(V,E)$ **covers** a node $v$ if some edge of $M$ is incident with $v$. A **perfect matching** is a matching that covers every node.
--
--   The convex hull of the characteristic vectors of perfect matchings is described by Theorem 6.3.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching

namespace CombOpt.MatchingPolytope

/-- **A perfect matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "we say that M covers a node v … if some edge of M is incident
with v. … A perfect matching is one that covers all the nodes."

`G.IsPerfectMatching M` says that `M` is a matching and every node is an end of some edge of `M`. -/
def Graph.IsPerfectMatching {V E : Type*} [Fintype E] (G : Graph V E) (M : Finset E) : Prop :=
  G.IsMatching M ∧ ∀ v : V, ∃ e ∈ M, v ∈ G.ends e

end CombOpt.MatchingPolytope


