-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
-- name    : RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:29.412091+00:00
-- url     : https://prove2.me/theorems/b84a6cef-f4fb-4085-9630-f5ab4be3890c
-- title:
--   §3, p. 159 and §4, p. 164 — ternary tree, branch-decomposition, width, branch-width β(G)
-- statement:
--   A **ternary tree** is a tree in which every vertex has valency $1$ or $3$; its vertices of valency $1$ are its **leaves**.
--
--   A **branch-decomposition** of a hypergraph $G$ is a pair $(T,\tau)$ where $T$ is a ternary tree and $\tau$ is a bijection from the set of leaves of $T$ to $E(G)$. The **order** of an edge $f$ of $T$ is the number of vertices $v$ of $G$ for which there are leaves $t_1,t_2$ in different components of $T\setminus f$ with $\tau(t_1),\tau(t_2)$ both incident with $v$. The **width** of $(T,\tau)$ is the maximum order of an edge of $T$, and the **branch-width** of $G$ is
--
--   $$\beta(G)=\min\{\text{width of }(T,\tau)\},$$
--
--   the minimum over all branch-decompositions of $G$, with $\beta(G)=0$ if $|E(G)|\le1$, when $G$ has no branch-decomposition.
--
--   Branch-width is the decomposition side of the minimax theorem $\max(\beta(G),\gamma(G))=\theta(G)$.
--
--   **Formalization Note** The tree has vertex set `Fin n`, and $\tau$ is stored as its inverse, an injective map from $E(G)$ onto the leaves of $T$. The order of the tree edge $uw$ counts the vertices incident both with an edge whose leaf is on $u$'s side of $T\setminus uw$ and with an edge whose leaf is on $w$'s side. When $|E(G)|\ge2$ a branch-decomposition exists, so the infimum in $\mathbb N$ is attained and is not a junk value.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 159 (ternary tree), p. 164 (branch-decomposition, width, branch-width)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph

namespace RobertsonSeymour1991.GM10.Minimax

variable {V E : Type}

/-- p. 159: a ternary tree: a tree in which every vertex has valency 1 or 3. -/
def IsTernaryTree {W : Type} (T : SimpleGraph W) : Prop :=
  T.IsTree ∧ ∀ w, (T.neighborSet w).ncard = 1 ∨ (T.neighborSet w).ncard = 3

/-- p. 164: a branch-decomposition `(T, τ)` of `G`; the tree is on `Fin n`, and `τ` is stored as the
inverse bijection `E(G) → leaves of T`. -/
structure BranchDecomposition (G : Hypergraph V E) (n : ℕ) where
  T : SimpleGraph (Fin n)
  ternary : IsTernaryTree T
  τ : E → Fin n
  τ_injective : Function.Injective τ
  τ_leaf : ∀ f, (T.neighborSet (τ f)).ncard = 1
  τ_onto_leaves : ∀ t, (T.neighborSet t).ncard = 1 → ∃ f, τ f = t

namespace BranchDecomposition

variable {G : Hypergraph V E} {n : ℕ}

/-- p. 164: the order of the edge `uw` of `T`. -/
noncomputable def edgeOrder (D : BranchDecomposition G n) (u w : Fin n) : ℕ :=
  {v : V | ∃ f₁ f₂ : E, G.inc f₁ v ∧ G.inc f₂ v ∧
    (D.T.deleteEdges {s(u, w)}).Reachable u (D.τ f₁) ∧
    (D.T.deleteEdges {s(u, w)}).Reachable w (D.τ f₂)}.ncard

/-- p. 164: the width, the maximum order of an edge of `T`. -/
noncomputable def width (D : BranchDecomposition G n) : ℕ :=
  sSup {k | ∃ u w, D.T.Adj u w ∧ D.edgeOrder u w = k}

end BranchDecomposition

/-- p. 164: the branch-width `β(G)` (`0` if `|E(G)| ≤ 1`). -/
noncomputable def branchWidth (G : Hypergraph V E) : ℕ :=
  if Nat.card E ≤ 1 then 0 else sInf {k | ∃ (n : ℕ) (D : BranchDecomposition G n), D.width = k}

end RobertsonSeymour1991.GM10.Minimax


