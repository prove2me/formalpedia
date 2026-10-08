-- Prove2me | Definitions.Def_SnarkGen_CycleCover_IsEvenEdgeSet
-- name    : SnarkGen_CycleCover_IsEvenEdgeSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:13.55359+00:00
-- url     : https://prove2.me/theorems/3c47b7f0-c5e3-4a9a-bf55-79f6d29a9f4c
-- title:
--   Even subgraph (Section 5)
-- statement:
--   An **even graph** is a graph in which every vertex has even degree. An even subgraph of a finite simple graph $G$ is recorded by its edge set: a set $S \subseteq E(G)$ is even when every vertex $v$ of $G$ lies on an even number of edges of $S$,
--
--   $$\bigl|\{ e \in S : v \in e \}\bigr| \ \text{is even for every vertex } v.$$
--
--   Even subgraphs are the colour classes of a $k$-CDC in the paper's "$k$-multiset of even subgraphs" form. The empty set is even.
--
--   **Formalization Note** Vertices not touched by $S$ have degree $0$ and are harmless; only the edge set matters.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 15, Section 5

import Mathlib

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, p. 15: an *even graph* is a graph where each vertex has even degree.
An even subgraph of `G` is recorded by its edge set `S ⊆ E(G)`: every vertex `v` lies on an
even number of edges of `S`. -/
def IsEvenEdgeSet {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset (Sym2 V)) :
    Prop :=
  (↑S : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ v : V, Even (S.filter (fun e => v ∈ e)).card

end SnarkGen.CycleCover


