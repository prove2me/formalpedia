-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Structure_TreeDecomposition
-- name    : RobertsonSeymour1991_GM10_Structure_TreeDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:49:10.041061+00:00
-- url     : https://prove2.me/theorems/37788882-ecb0-4490-9094-8823ee294674
-- title:
--   §5, p. 168 — tree-decomposition (T, τ) of a hypergraph, its width, tree-width ω(G)
-- statement:
--   A **tree-decomposition** of a hypergraph $G$ is a pair $(T, \tau)$, where $T$ is a tree and, for $t \in V(T)$, $\tau(t)$ is a subhypergraph of $G$, such that
--
--   1. $\bigcup_{t \in V(T)} \tau(t) = G$;
--   2. for distinct $t, t' \in V(T)$, $E(\tau(t) \cap \tau(t')) = \emptyset$;
--   3. for $t, t', t'' \in V(T)$, if $t'$ is on the path of $T$ between $t$ and $t''$, then $\tau(t) \cap \tau(t'') \subseteq \tau(t')$.
--
--   The **width** of $(T,\tau)$ is $\max_{t}(|V(\tau(t))| - 1)$ and the **tree-width** of $G$ is the minimum width of a tree-decomposition,
--   $$\omega(G) = \min_{(T,\tau)} \max_{t \in V(T)} \bigl(|V(\tau(t))| - 1\bigr),$$
--   so that $\omega(G) = -1$ when $V(G) = \emptyset$.
--
--   **Formalization Note** The tree is a `SimpleGraph` on `Fin n` with `IsTree` (so $n \ge 1$); "the path between $t$ and $t''$" is any path walk, which is unique in a tree. `WidthLE D w` says every bag has at most $w+1$ vertices, in $\mathbb Z$. `treeWidth` is the `sInf` in $\mathbb Z$ of the admissible $w$; that set is nonempty (the one-node decomposition $\tau = G$) and bounded below by $-1$, so the infimum is the minimum, not a junk value.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 168, §5 (tree-decomposition, width, tree-width)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Hypergraph

namespace RobertsonSeymour1991.GM10.Structure

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

end RobertsonSeymour1991.GM10.Structure


