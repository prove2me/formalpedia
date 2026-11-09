-- Prove2me | Definitions.Def_HypClass1_IsPerfectMatchingBip
-- name    : HypClass1_IsPerfectMatchingBip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:48.098197+00:00
-- url     : https://prove2.me/theorems/ee044747-36ce-4f92-a8cd-d9bdb93ff702
-- title:
--   Perfect matching of a bipartite graph
-- statement:
--   A set $M$ of edges of a bipartite graph with parts $X, Y$ is a **perfect matching** if every vertex of $X$ and every vertex of $Y$ lies in exactly one edge of $M$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §6, Lemma 6.1 and Proposition 6.2, pp.15–16

import Mathlib
import Definitions.Def_HypClass1_IsPseudorandomBip

namespace HypClass1

/-- **Perfect matching of a bipartite graph** with parts `X`, `Y`: a set of edges `M ⊆ X × Y` in which
every vertex of `X` and every vertex of `Y` lies in exactly one edge. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §6 pp.15–16
(Lemma 6.1, Proposition 6.2). -/
def IsPerfectMatchingBip {α β : Type*} [DecidableEq α] [DecidableEq β] (X : Finset α)
    (Y : Finset β) (M : Finset (α × β)) : Prop :=
  M ⊆ X ×ˢ Y ∧ (∀ x ∈ X, ldeg M x = 1) ∧ (∀ y ∈ Y, rdeg M y = 1)

end HypClass1


