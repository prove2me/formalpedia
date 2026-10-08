-- Prove2me | Definitions.Def_SnarkGen_CycleCover_IsTwoRegularEdgeSet
-- name    : SnarkGen_CycleCover_IsTwoRegularEdgeSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:14.611432+00:00
-- url     : https://prove2.me/theorems/f667d292-9559-4291-b583-f2257a3168c0
-- title:
--   2-regular subgraph, as a set of edges
-- statement:
--   A **2-regular subgraph** of a finite simple graph $G$ is recorded by its edge set $D \subseteq E(G)$: every vertex $v$ of $G$ lies on either no edge of $D$ or exactly two edges of $D$,
--
--   $$\bigl|\{ e \in D : v \in e \}\bigr| \in \{0, 2\} \quad \text{for every vertex } v.$$
--
--   Such a $D$ is a union of vertex-disjoint cycles of $G$. It need not be spanning, and it may be empty. A **2-factor** is the spanning case, in which every vertex lies on exactly two edges of $D$. The size $|D|$ is the number of edges, which equals the number of vertices that $D$ touches.
--
--   **Formalization Note** This is the subgraph appearing in Proposition 5.3 ("any 2-regular subgraph") and Lemma 7.2; it is the edge-set form of Mathlib's `SimpleGraph.IsCycles`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 15, Proposition 5.3; p. 24, Lemma 7.2

import Mathlib

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, Proposition 5.3 (p. 15) and Lemma 7.2 (p. 24): a *2-regular subgraph*
of `G`, recorded by its edge set `D ⊆ E(G)`: every vertex lies on either no edge or exactly two
edges of `D`. This is a vertex-disjoint union of cycles of `G`, not necessarily spanning and
possibly empty. -/
def IsTwoRegularEdgeSet {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (D : Finset (Sym2 V)) : Prop :=
  (↑D : Set (Sym2 V)) ⊆ G.edgeSet ∧
    ∀ v : V, (D.filter (fun e => v ∈ e)).card = 0 ∨ (D.filter (fun e => v ∈ e)).card = 2

end SnarkGen.CycleCover


