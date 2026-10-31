-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_shrink
-- name    : CombOpt_TutteBerge_Multigraph_shrink
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:18.173448+00:00
-- url     : https://prove2.me/theorems/2a3ed925-5f67-4d95-b87f-cfc3f325625a
-- title:
--   Shrinking: the graph $G\times C$
-- statement:
--   Let $S\subseteq V$. The graph obtained by **shrinking** $S$ has node set $(V\setminus S)\cup\{C\}$, where $C$ is one new node, and edge set $E\setminus\gamma(S)$. If $v$ is an end of $e$ in $G$, then $v$ is an end of $e$ in the new graph when $v\notin S$, and otherwise $C$ is.
--
--   For an odd circuit $C$ of $G$, the book's $G\times C$ is this graph with $S=V(C)$.
--
--   **Formalization Note** The new node is `none` in `Option {v // v ∉ S}`. The edges are the subtype of $E$ outside $\gamma(S)$, so every edge keeps its identity and parallel edges stay distinct.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_edgesWithin

namespace CombOpt.TutteBerge

open scoped Classical in
/-- **Shrinking a node set: G × C for `S = V(C)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 131 (PDF p. 139): "We define G′ = G × C, the subgraph obtained from G by shrinking C,
as follows. G × C has node-set (V\V(C)) ∪ {C} and edge-set E\γ(V(C)); for each edge e of G′ and end
v of e in G, v is an end of e in G′ if v ∉ V(C), and otherwise C is an end of e in G′."

The new node `C` is `none`; the old nodes outside `S` are the `some v`. An edge keeps its identity:
the edges of `G.shrink S` are the edges of `G` outside `γ(S)`.

**Formalization Note.** Defined for any node set `S`; the book's G × C is `G.shrink C.nodeSet` for
an odd circuit `C`. Parallel edges may arise, and survive as distinct edges, which is what lets
Proposition 5.4 say `M ⊆ M′ ∪ E(C)`. -/
noncomputable def Multigraph.shrink {V E : Type*} (G : Multigraph V E) (S : Set V) :
    Multigraph (Option {v : V // v ∉ S}) {e : E // e ∉ G.edgesWithin S} where
  ends e := Sym2.map (fun v => if h : v ∈ S then none else some ⟨v, h⟩) (G.ends e.1)

end CombOpt.TutteBerge


