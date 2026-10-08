-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition
-- name    : RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:32.148187+00:00
-- url     : https://prove2.me/theorems/e375a2af-0e88-4a84-bf10-456bea7e94e9
-- title:
--   §5, p. 168 — tree-decomposition of a hypergraph, its width, and the tree-width ω(G)
-- statement:
--   A **tree-decomposition** of a hypergraph $G$ is a pair $(T, \tau)$, where $T$ is a tree and, for each $t \in V(T)$, $\tau(t)$ is a subhypergraph of $G$, such that
--
--   1. $\bigcup(\tau(t) : t \in V(T)) = G$;
--   2. for distinct $t, t' \in V(T)$, $E(\tau(t) \cap \tau(t')) = \emptyset$;
--   3. for $t, t', t'' \in V(T)$, if $t'$ is on the path of $T$ between $t$ and $t''$ then $\tau(t) \cap \tau(t'') \subseteq \tau(t')$.
--
--   The **width** of such a tree-decomposition is $\max_{t \in V(T)} (|V(\tau(t))| - 1)$, and the **tree-width** of $G$ is
--   $$\omega(G) = \min\{\text{width of } (T,\tau) : (T,\tau) \text{ a tree-decomposition of } G\}.$$
--   Thus $\omega(G) \ge 0$ unless $V(G) = \emptyset$, when $\omega(G) = -1$.
--
--   Unlike the usual vertex-bag tree-decompositions of graphs, each part $\tau(t)$ here is a subhypergraph, and every edge of $G$ belongs to exactly one part.
--
--   **Formalization Note** The tree is a `SimpleGraph` on `Fin n` satisfying `IsTree` (connected, hence nonempty, and acyclic); condition (i) is two covering equalities (vertices and edges); "the path between $t$ and $t''$" is any `Walk.IsPath`, unique in a tree. Widths are integers so that $\omega = -1$ for the empty vertex set. `WidthLE D w` says every part has $|V(\tau(t))| - 1 \le w$, and $\omega(G)$ is the `sInf` in $\mathbb Z$ of all such $w$. That set is nonempty (the one-vertex tree with $\tau = G$) and bounded below by $-1$ (a tree has a vertex), so the `sInf` is the minimum width.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 168 (§5, tree-decomposition, width, tree-width); p. 159 (tree)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph

namespace RobertsonSeymour1991.GM10.TreeWidth

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

/-- p. 168: the tree-width `ω(G)` (`−1` if `V(G) = ∅`). -/
noncomputable def treeWidth (G : Hypergraph V E) : ℤ :=
  sInf {w : ℤ | ∃ (n : ℕ) (D : TreeDecomposition G n), D.WidthLE w}

end RobertsonSeymour1991.GM10.TreeWidth


