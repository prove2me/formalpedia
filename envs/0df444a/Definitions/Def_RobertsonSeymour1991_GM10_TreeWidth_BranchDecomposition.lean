-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_BranchDecomposition
-- name    : RobertsonSeymour1991_GM10_TreeWidth_BranchDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:16:28.551977+00:00
-- url     : https://prove2.me/theorems/eb2e5a12-aba3-4c92-ab70-e7337d60f6ed
-- title:
--   §4, p. 164 — branch-decomposition, its width, and the branch-width β(G)
-- statement:
--   A **tree** is a connected non-null graph with no circuits; its vertices of valency at most $1$ are its leaves, and it is **ternary** if every vertex has valency $1$ or $3$ (p. 159).
--
--   A **branch-decomposition** of a hypergraph $G$ is a pair $(T, \tau)$ where $T$ is a ternary tree and $\tau$ is a bijection from the set of leaves of $T$ to $E(G)$. The **order** of an edge $f$ of $T$ is the number of vertices $v$ of $G$ such that there are leaves $t_1, t_2$ of $T$ in different components of $T \setminus f$ with $\tau(t_1)$ and $\tau(t_2)$ both incident with $v$. The **width** of $(T, \tau)$ is the maximum order of an edge of $T$, and the **branch-width** of $G$ is
--   $$\beta(G) = \min\{\text{width of } (T,\tau) : (T,\tau) \text{ a branch-decomposition of } G\},$$
--   or $\beta(G) = 0$ if $|E(G)| \le 1$, when $G$ has no branch-decompositions.
--
--   Branch-width is one of the two width parameters compared in (5.1).
--
--   **Formalization Note** The tree is a `SimpleGraph` on `Fin n` (trees have no loops or parallel edges). The bijection $\tau$ is stored as its inverse, an injective map $E(G) \to$ `Fin n` landing on the leaves and onto them. The order of the tree edge $uw$ counts the vertices incident with an edge whose leaf lies on $u$'s side of $T \setminus uw$ and with an edge whose leaf lies on $w$'s side. For $|E(G)| \ge 2$ a branch-decomposition always exists, so the `sInf` in $\mathbb N$ is a true minimum; the case $|E(G)| \le 1$ is set to $0$ explicitly.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 159 (tree, leaf, ternary tree), p. 164 (§4, branch-decomposition, order, width, branch-width)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph

namespace RobertsonSeymour1991.GM10.TreeWidth

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

end RobertsonSeymour1991.GM10.TreeWidth


