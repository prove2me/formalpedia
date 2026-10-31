-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_gamma
-- name    : CombOpt_SpanningTree_Graph_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:06.175786+00:00
-- url     : https://prove2.me/theorems/2b9738a3-6e17-4d38-8080-b64aec2a4d9f
-- title:
--   Edges inside a node set, $\gamma(S)$
-- statement:
--   For a set $S\subseteq V$ of nodes,
--   $$\gamma(S)=\{e\in E : \text{both ends of } e \text{ are in } S\}.$$
--   A loop at a node of $S$ lies in $\gamma(S)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph

namespace CombOpt.SpanningTree

open Classical in
/-- **The edge set γ(S) inside a node set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12 (PDF p. 21): "by γ(A) the set {e ∈ E : both ends of e are in A}".

`G.gamma S` is the set of edges both of whose ends lie in `S`.

**Formalization Note.** A loop at a node of `S` is in `γ(S)`. -/
noncomputable def Graph.gamma {V E : Type*} [Fintype E] (G : Graph V E) (S : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => ∀ a ∈ G.ends e, a ∈ S)

end CombOpt.SpanningTree


