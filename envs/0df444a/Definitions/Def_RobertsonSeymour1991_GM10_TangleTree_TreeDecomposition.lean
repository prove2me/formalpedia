-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TreeDecomposition
-- name    : RobertsonSeymour1991_GM10_TangleTree_TreeDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:58.906686+00:00
-- url     : https://prove2.me/theorems/ee96d1eb-d0af-4bea-865e-5dbd20f5171f
-- title:
--   §5, p. 168 — tree-decomposition (T, τ) of a hypergraph, its width, tree-width ω(G)
-- statement:
--   A **tree-decomposition** of a hypergraph $G$ is a pair $(T,\tau)$, where $T$ is a tree and, for each $t\in V(T)$, $\tau(t)$ is a subhypergraph of $G$, such that
--
--   1. $\bigcup(\tau(t): t\in V(T)) = G$;
--   2. for distinct $t,t'\in V(T)$, $E(\tau(t)\cap\tau(t'))=\emptyset$;
--   3. for $t,t',t''\in V(T)$, if $t'$ is on the path of $T$ between $t$ and $t''$ then
--   $$\tau(t)\cap\tau(t'')\subseteq\tau(t').$$
--
--   The **width** is $\max_{t}(|V(\tau(t))|-1)$ and the **tree-width** $\omega(G)$ is the minimum width of a tree-decomposition ($\omega(G)=-1$ when $V(G)=\emptyset$).
--
--   In this mission tree-decompositions are the output of the tangle-tree theorem; width is not used, but the module is kept whole because it is shared with the other missions of the series.
--
--   **Formalization Note** The tree $T$ is a `SimpleGraph` on `Fin n` that is a tree (in particular nonempty, so $n\ge 1$). Condition 1 is written as two covering equalities (vertices and edges); "the path between $t$ and $t''$" is any `Walk.IsPath`, which is unique in a tree. Width is computed in $\mathbb Z$ so that $\omega(G)=-1$ when $V(G)=\emptyset$; the set of admissible widths is nonempty and bounded below by $-1$, so the `sInf` is a minimum.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 168, definition of tree-decomposition, width and tree-width

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TangleTree

variable {V E : Type}

/-- p. 168: a tree-decomposition `(T, τ)` of `G`. -/
structure TreeDecomposition (G : Hypergraph V E) (n : ℕ) where
  T : SimpleGraph (Fin n)
  isTree : T.IsTree
  τ : Fin n → G.Sub
  verts_cover : (⋃ t, (τ t).verts) = Set.univ
  edges_cover : (⋃ t, (τ t).edges) = Set.univ
  edges_disjoint : ∀ t t', t ≠ t' → (τ t).edges ∩ (τ t').edges = ∅
  path : ∀ (t t' t'' : Fin n) (p : T.Walk t t''), p.IsPath → t' ∈ p.support →
    ((τ t).inter (τ t'')).le (τ t')

/-- p. 168: `(T, τ)` has width at most `w`: `|V(τ(t))| − 1 ≤ w` for every `t`. -/
def TreeDecomposition.WidthLE {G : Hypergraph V E} {n : ℕ} (D : TreeDecomposition G n) (w : ℤ) : Prop :=
  ∀ t, ((D.τ t).verts.ncard : ℤ) - 1 ≤ w

end RobertsonSeymour1991.GM10.TangleTree


