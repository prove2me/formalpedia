-- Prove2me | Definitions.Def_NetBilinear_Supplement_ForestConditions
-- name    : NetBilinear_Supplement_ForestConditions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:43:37.181804+00:00
-- url     : https://prove2.me/theorems/40bdd28a-7508-4b26-9fe8-266fd9863eb3
-- title:
--   The forest structure of Theorem 3: conditions (i)–(iii) of Propositions 4 and 6 (corrected: Prop. 6 (iii) over $\tilde{\mathcal I}\cup\tilde{\mathcal I}^j$)
-- statement:
--   Let $G=(V,A)$ be a network with undirected variant $\bar G$, let $\tilde{\mathcal I}^j\subseteq V$ ($j\in M$) be node sets, $\tilde{\mathcal I}\subseteq V$ the **connection nodes**, $\tilde{\mathcal J}\subseteq A$ the **connection arcs**, and let the class $l$ have base term $y_{j'}x_{i'}$. For each $j$, let $\bar F^j$ be a forest of the parallel network $G^j$ composed of trees $\bar T^j_k$, $k\in\Gamma_j$. The data satisfy the conditions of Theorem 3 when:
--
--   Proposition 4:
--   1. each $\bar T^j_k$ is a tree of $\bar G$, the trees of $\bar F^j$ are node-disjoint, and their nodes are exactly $\tilde{\mathcal I}^j$;
--   2. the collection of all trees $\bar T^j_k$ ($k\in\Gamma_j$, $j\in M$) is vertically connected through $\tilde{\mathcal I}$ and $\tilde{\mathcal J}$ (Definition 2);
--   3. $\bigcup_{j}\tilde{\mathcal I}^j\cup\tilde{\mathcal I}$ is the node set of a tree of $\bar G$, and every arc of $\tilde{\mathcal J}$ has an endpoint in it.
--
--   Proposition 6:
--   1. either $i'\in\tilde{\mathcal J}$ or $i'$ is incident to exactly one node of $\tilde{\mathcal I}\cup\tilde{\mathcal I}^{j'}$, but not both;
--   2. each arc of $\tilde{\mathcal J}$ is incident to at most one node of $\tilde{\mathcal I}\cup\tilde{\mathcal I}^j$, for each $j\in M$;
--   3. each node of $\tilde{\mathcal I}\cap\tilde{\mathcal I}^j$ is adjacent to no other node of $\tilde{\mathcal I}\cup\tilde{\mathcal I}^j$ and incident to no arc of $\tilde{\mathcal J}$ (for $j=j'$: of $\tilde{\mathcal J}\cup\{i'\}$).
--
--   These are exactly the hypotheses of Theorem 3, the converse of Propositions 4 and 6.
--
--   **Formalization Note** Condition 3 of Proposition 6 is printed with "adjacent to no other nodes in that set", that set being $\tilde{\mathcal I}\cap\tilde{\mathcal I}^j$. Under that reading Theorem 3 is false (counterexample in the item `NetBilinear.Supplement.theorem_3`). The proof of Proposition 6 (iii), p.18, excludes every other flow-balance constraint creating the term, i.e. every node of $\tilde{\mathcal I}\cup\tilde{\mathcal I}^j$, and that is the condition stated here. The forest is given by its trees, a finite family (`Fintype (Γ j)`). Trees are subgraphs of $\bar G$ whose induced graph is a tree, so they are nonempty. An arc is incident to a node set when its tail or head lies in it.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Proposition 4 (i)–(iii), p.12; Proposition 6 (i)–(iii), p.17 and its proof p.18; Theorem 3, p.18

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_Supplement_VerticallyConnected

namespace NetBilinear.Supplement

/-- **The forest structure of Theorem 3: conditions (i)–(iii) of Propositions 4 and 6.**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, Proposition 4 (i)–(iii), p.12, and Proposition 6 (i)–(iii), p.17, used as
hypotheses by Theorem 3, p.18.

Data: a network `G` (with undirected variant `Ḡ`), node sets `Ĩ_j = It j` (`j ∈ M`), the
connection node set `Ĩ = Ic`, the connection arc set `J̃ = Jc`, the class `l` through its pair
`(i', j')` (`A^l_{j'i'} = 1`, base term `y_{j'} x_{i'}`), and for each `j` a forest `F̄^j` of the
parallel network `G^j` given by its trees `T̄^j_k = T j k`, `k ∈ Γ_j`.

Proposition 4:
* (i) "the forest F̄j is composed of the nodes in Ĩj": every `T̄^j_k` is a tree of `Ḡ`, the trees
  of one forest are node-disjoint, and their node sets cover exactly `Ĩ_j`;
* (ii) "the collection of the trees T̄jk for all k ∈ Γj and all j ∈ M are vertically connected
  through connection nodes Ĩ and connection arcs J̃" (Definition 2);
* (iii) "the collection of all nodes in F̄j for all j ∈ M together with the connection nodes Ĩ
  form a tree in G, which has at least one incident node to each connection arc in J̃".

Proposition 6:
* (i) "arc i′ is either in J̃ or incident to exactly one node in Ĩ ∪ Ĩj′, but not both";
* (ii) "each arc in J̃ is incident to at most one node in Ĩ ∪ Ĩj for each j ∈ M";
* (iii) each node of `Ĩ ∩ Ĩ_j` is adjacent to no other node of `Ĩ ∪ Ĩ_j` and incident to no arc
  of `J̃` (for `j = j'`: of `J̃ ∪ {i′}`).

**Formalization Note.** (Correction.) Proposition 6 (iii) as printed says the node "is
adjacent to no other nodes in that set", where "that set" reads as `Ĩ ∩ Ĩ_j`. With that
reading Theorem 3 is false (counterexample in the Differences of `NetBilinear.Supplement.theorem_3`);
the proof of Proposition 6 (iii), p.18 ("the flow-balance constraint at node h(k) … and at node
t(k) … cannot be included in the aggregation") excludes every other node of `Ĩ ∪ Ĩ_j`, and
that is the condition stated here. The forest `F̄^j` is the node-disjoint union of its trees,
so it is given by them; `Γ_j` is finite (disjoint nonempty node sets in a finite `V`). Trees
are subgraphs of `Ḡ` whose induced graph `coe` is a tree (`SimpleGraph.IsTree`, nonempty),
with the replica naming convention of p.12; "adjacent" is adjacency in `Ḡ`; an arc is
incident to a node set when its tail or head lies in it. -/
structure ForestConditions {V A M : Type*} [DecidableEq V] [Fintype M]
    (G : Network V A) (It : M → Finset V) (Ic : Finset V) (Jc : Finset A) (i' : A) (j' : M)
    (Γ : M → Type*) [∀ j, Fintype (Γ j)] (T : (j : M) → Γ j → G.underlying.Subgraph) :
    Prop where
  /-- Prop. 4 (i): each `T̄^j_k` is a tree of `Ḡ`. -/
  tree : ∀ j k, (T j k).coe.IsTree
  /-- Prop. 4 (i): the trees of the forest `F̄^j` are node-disjoint. -/
  disjoint : ∀ j (k k' : Γ j), k ≠ k' → Disjoint (T j k).verts (T j k').verts
  /-- Prop. 4 (i): the nodes of the forest `F̄^j` are exactly `Ĩ_j`. -/
  cover : ∀ j v, v ∈ It j ↔ ∃ k, v ∈ (T j k).verts
  /-- Prop. 4 (ii): all trees `T̄^j_k` are vertically connected through `Ĩ` and `J̃`. -/
  vconn : VerticallyConnected G (fun b : (Σ j, Γ j) => (T b.1 b.2).verts) (Ic : Set V)
    (Jc : Set A)
  /-- Prop. 4 (iii): `⋃_j Ĩ_j ∪ Ĩ` is the node set of a tree of `Ḡ`. -/
  union_tree : ∃ T₀ : G.underlying.Subgraph,
    T₀.verts = ((Ic ∪ Finset.univ.biUnion It : Finset V) : Set V) ∧ T₀.coe.IsTree
  /-- Prop. 4 (iii): every connection arc has an endpoint in `⋃_j Ĩ_j ∪ Ĩ`. -/
  arc_meets_union : ∀ a ∈ Jc, ArcIncToSet G a ((Ic ∪ Finset.univ.biUnion It : Finset V) : Set V)
  /-- Prop. 6 (i): `i' ∈ J̃` or `i'` has exactly one endpoint in `Ĩ ∪ Ĩ_{j'}`, but not both. -/
  base_arc : Xor (i' ∈ Jc) (Xor (G.tail i' ∈ Ic ∪ It j') (G.head i' ∈ Ic ∪ It j'))
  /-- Prop. 6 (ii): each connection arc has at most one endpoint in `Ĩ ∪ Ĩ_j`, for each `j`. -/
  conn_arc : ∀ a ∈ Jc, ∀ j, ¬ (G.tail a ∈ Ic ∪ It j ∧ G.head a ∈ Ic ∪ It j)
  /-- Prop. 6 (iii) (corrected reading, see the Formalization Note): a node of `Ĩ ∩ Ĩ_j` is
  adjacent to no node of `Ĩ ∪ Ĩ_j`, incident to no arc of `J̃`, and, for `j = j'`, not an
  endpoint of `i'`. -/
  double_node : ∀ j, ∀ v ∈ Ic ∩ It j,
    (∀ w ∈ Ic ∪ It j, ¬ G.underlying.Adj v w) ∧ (∀ a ∈ Jc, G.tail a ≠ v ∧ G.head a ≠ v) ∧
    (j = j' → G.tail i' ≠ v ∧ G.head i' ≠ v)

end NetBilinear.Supplement


