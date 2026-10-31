-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_Graph_matchingIndep
-- name    : CombOpt_MatroidPolytope_Graph_matchingIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:36.223995+00:00
-- url     : https://prove2.me/theorems/96351684-584a-4d12-87da-79963efc5b1e
-- title:
--   Node sets covered by a matching
-- statement:
--   For a graph $G=(V,E)$ let
--   $$\mathcal I=\{J\subseteq V : \text{some matching } M' \text{ of } G \text{ covers every node of } J\}.$$
--   A matching covers a node $v$ if some edge of the matching is incident with $v$; $M'$ may cover nodes outside $J$ as well. With ground set $S=V$, this family is the independent-set family of the **matching matroid** of $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 276 (PDF p. 283); covering, §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_Graph_IsMatching

namespace CombOpt.MatroidPolytope

/-- **The independent sets of the matching matroid.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 276 (PDF p. 283): "Let G = (V, E) be a graph, let S = V, and let
I = {J ⊆ S : there is a matching M′ of G covering all the elements of J}. (Notice that M′ may
cover other nodes in addition.)"

`G.matchingIndep J` says that some matching `M'` of `G` covers every node of `J`, i.e. every
`v ∈ J` is an end of some edge of `M'` ("M covers a node v … if some edge of M is incident with
v", p. 127). -/
def Graph.matchingIndep {V E : Type*} (G : Graph V E) (J : Finset V) : Prop :=
  ∃ M' : Finset E, G.IsMatching M' ∧ ∀ v ∈ J, ∃ e ∈ M', v ∈ G.ends e

end CombOpt.MatroidPolytope


