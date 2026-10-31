-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsPerfectMatching
-- name    : CombOpt_TJoin_Graph_IsPerfectMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:24.930984+00:00
-- url     : https://prove2.me/theorems/61087784-56b4-4549-9387-085107b6f249
-- title:
--   Perfect matching
-- statement:
--   A **matching** of $G=(V,E)$ is a set $M\subseteq E$ such that no node is incident with more than one edge of $M$; it is **perfect** if it covers every node. Equivalently, every node is an end of exactly one edge of $M$.
--
--   **Formalization Note** The mission uses perfect matchings only for loopless graphs (Theorem 5.13, corrected).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph

namespace CombOpt.TJoin

/-- **Perfect matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "A matching in a graph G = (V, E) is a set M of edges such that
no node of G is incident with more than one edge in M. … A perfect matching is one that covers
all the nodes." An edge is incident with each of its ends (p. 9).

`G.IsPerfectMatching M` holds when every node is an end of exactly one edge of `M`.

**Formalization Note.** "No node incident with more than one edge" plus "every node covered"
is "every node incident with exactly one edge". This mission uses perfect matchings only in
loopless graphs (Theorem 5.13, corrected). -/
def Graph.IsPerfectMatching {V E : Type*} [Fintype E] [DecidableEq V] (G : Graph V E)
    (M : Finset E) : Prop :=
  ∀ v : V, (M.filter (fun e => v ∈ G.ends e)).card = 1

end CombOpt.TJoin


