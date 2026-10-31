-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_IsSpanningTreeDelete
-- name    : CombOpt_HeldKarp_Graph_IsSpanningTreeDelete
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:26.552556+00:00
-- url     : https://prove2.me/theorems/611f2ba1-cd7f-4da2-9f67-3e1e7b2aba3e
-- title:
--   Spanning tree of $G\setminus v_1$
-- statement:
--   Let $v_1$ be a node of $G$, and let $G\setminus v_1$ be the graph obtained by deleting $v_1$ and the edges incident with it. A set $T$ of edges is a **spanning tree of $G\setminus v_1$** if
--
--   1. no edge of $T$ has $v_1$ as an end;
--   2. any two nodes different from $v_1$ are joined by a path all of whose edges lie in $T$;
--   3. $T$ is a forest.
--
--   When $V=\{v_1\}$, the empty set is the spanning tree of the empty graph $G\setminus v_1$.
--
--   **Formalization Note** $G\setminus v_1$ is not built as a separate graph: its edges are the edges of $G$ not incident with $v_1$, and its paths and circuits are those of $G$ using only such edges.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, p. 253 (PDF p. 261); §2.1, pp. 10–11

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_IsForest

namespace CombOpt.HeldKarp

/-- **T is a spanning tree of G \ v₁.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, p. 253
(PDF p. 261): "the graph G \ v_1 we get by deleting v_1 and the incident edges from G"; a spanning
tree is a connected forest containing every node (§2.1, pp. 10–11).

`G.IsSpanningTreeDelete v₁ T` says: no edge of `T` has `v₁` as an end, any two nodes different from
`v₁` are joined by a path all of whose edges lie in `T`, and `T` contains no circuit.

**Formalization Note.** `G \ v₁` is not built as a separate graph: its edges are the edges of `G`
without `v₁` among their ends, and its paths are the paths of `G` using only such edges (such a path
never visits `v₁`, except as a one-node path when it starts there, which the connectivity clause
excludes). A circuit of `G \ v₁` is a circuit of `G` with edges in `T`. When `V = {v₁}` the empty
edge set is the spanning tree of the empty graph `G \ v₁`. -/
def Graph.IsSpanningTreeDelete {V E : Type*} (G : Graph V E) (v₁ : V) (T : Finset E) : Prop :=
  (∀ e ∈ T, v₁ ∉ G.ends e) ∧
  (∀ u w : V, u ≠ v₁ → w ≠ v₁ → ∃ p : G.Walk u w, ∀ e ∈ p.edges, e ∈ T) ∧
  G.IsForest T

end CombOpt.HeldKarp


