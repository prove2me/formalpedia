-- Prove2me | Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
-- name    : ChvatalPolytopes_Separation_AlphaCritical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:17:01.775031+00:00
-- url     : https://prove2.me/theorems/4f7bdff9-a75f-44d7-85cb-6f164e6d46e6
-- title:
--   Critical edges, the critical graph $G^*$ and $\alpha$-critical graphs (§4)
-- statement:
--   Let $G=(V,E)$ be a finite graph and $\alpha(G)$ its **stability number**, the largest size of a stable set of $G$. For an edge $e\in E$ write $G-e=(V,E\setminus\{e\})$.
--
--   1. An edge $e$ of $G$ is **critical** if
--   $$\alpha(G-e)=\alpha(G)+1.$$
--   2. $E^*$ is the set of critical edges of $G$ and $G^*=(V,E^*)$ is the spanning subgraph formed by them.
--   3. $G$ is **$\alpha$-critical** if all of its edges are critical.
--
--   Critical edges are those whose removal enlarges the stability number; $G^*$ carries the connectivity hypothesis of Theorem 4.2, and $\alpha$-critical graphs are the subject of Corollary 4.3.
--
--   **Formalization Note** $\alpha$ is Mathlib's natural-number-valued `indepNum`; $G-e$ is `G.deleteEdges {e}`; $G^*$ is `SimpleGraph.fromEdgeSet` of the critical edges. A graph without edges is $\alpha$-critical vacuously, as on the page.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 143, §4 (definitions of critical edge and α-critical graph; E*, G* in Theorem 4.2)

import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Critical edge** (Chvátal 1975, p. 143): an edge `e` of `G` is *critical* if
`α(G − e) = α(G) + 1`, where `α = indepNum` is the stability number and `G − e` is `G` with the
edge `e` deleted. -/
def IsCriticalEdge {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ (G.deleteEdges {e}).indepNum = G.indepNum + 1

/-- The spanning subgraph `G* = (V, E*)` of `G` whose edges are the critical edges of `G`
(Chvátal 1975, p. 143, Theorem 4.2). -/
def criticalGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | IsCriticalEdge G e}

/-- **α-critical graph** (Chvátal 1975, p. 143): a graph all of whose edges are critical. -/
def IsAlphaCritical {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, IsCriticalEdge G e

end ChvatalPolytopes.Separation


