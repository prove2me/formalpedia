-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
-- name    : CombOpt_MatchingPolytope_Graph_IsMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:26.304986+00:00
-- url     : https://prove2.me/theorems/df14a7ff-b53b-4dbd-ae36-6d0331d9ff3e
-- title:
--   A matching of a graph
-- statement:
--   A **matching** of a graph $G=(V,E)$ is a set $M\subseteq E$ of edges such that no node of $G$ is incident with more than one edge of $M$; an edge is incident with each of its ends.
--
--   Matchings are the combinatorial objects whose characteristic vectors span the matching polytope $M(G)$.
--
--   **Formalization Note** For every node $v$, at most one edge of $M$ has $v$ among its ends. The theorems of the mission that use matchings assume $G$ loopless.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CombOpt.MatchingPolytope

open Classical in
/-- **A matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "A matching in a graph G = (V, E) is a set M of edges such
that no node of G is incident with more than one edge in M."

`G.IsMatching M` says that every node is an end of at most one edge of `M`.

**Formalization Note.** An edge is incident with each of its ends (p. 9). The statements of this
mission that use matchings assume `G` loopless, so the question of how a loop is counted does not
arise there. -/
def Graph.IsMatching {V E : Type*} [Fintype E] (G : Graph V E) (M : Finset E) : Prop :=
  ∀ v : V, (M.filter (fun e => v ∈ G.ends e)).card ≤ 1

end CombOpt.MatchingPolytope


