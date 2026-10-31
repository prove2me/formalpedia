-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_gamma
-- name    : CombOpt_MatchingPolytope_Graph_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:56.488953+00:00
-- url     : https://prove2.me/theorems/967b14df-93f1-4f36-84c0-fc75647fdbc6
-- title:
--   The edge set $\gamma(S)$ induced by a node set
-- statement:
--   For a graph $G=(V,E)$ and $S\subseteq V$, $\gamma(S)$ is the set of edges both of whose ends lie in $S$:
--   $$\gamma(S)=\{e\in E:\ \text{both ends of } e \text{ are in } S\}.$$
--
--   The blossom constraints $x(\gamma(S))\le(|S|-1)/2$ of (6.7) and the identity (6.9) are sums over $\gamma(S)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CombOpt.MatchingPolytope

open Classical in
/-- **The edge set γ(S) inside a node set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12 (PDF p. 21): "by γ(A) the set {e ∈ E : both ends of e are in A}".

`G.gamma S` is the set of edges both of whose ends lie in `S`.

**Formalization Note.** A loop at a node of `S` is in `γ(S)`. -/
noncomputable def Graph.gamma {V E : Type*} [Fintype E] (G : Graph V E) (S : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => ∀ a ∈ G.ends e, a ∈ S)

end CombOpt.MatchingPolytope


