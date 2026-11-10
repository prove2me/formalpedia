-- Prove2me | Definitions.Def_TwoConnSS_IsContractible
-- name    : TwoConnSS_IsContractible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:45.76365+00:00
-- url     : https://prove2.me/theorems/d9fa0d3a-a06f-4872-ac52-f0e90443d55f
-- title:
--   $\beta$-contractible subgraphs
-- statement:
--   Let $G$ be a graph and $\beta > 1$. A nontrivial 2EC subgraph $H = (X, E_H)$ of $G$ (with $E_H \subseteq E(G)$ inside $X$, $|X| \ge 2$, and $(X, E_H)$ 2EC) is **$\beta$-contractible** if every 2ECSS $F$ of $G$ satisfies
--   $$|F \cap E(G[X])| \ge |E_H|/\beta.$$
--
--   Preprocessing removes small contractible subgraphs: any solution must spend nearly $|E_H|$ edges inside them anyway.
--
--   **Formalization Note** $H$ must have at least two vertices; for a single vertex the inequality reads $0 \ge 0$, and excluding such subgraphs would exclude every graph.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Definition 6.8, p.26

import Mathlib
import Definitions.Def_TwoConnSS_blocks

namespace TwoConnSS

variable {V : Type*} [Fintype V]

/-- A nontrivial 2EC subgraph `H = (X, E_H)` of `G`: `E_H ⊆ E(G)`, every edge of `E_H` has both ends
in `X`, `|X| ≥ 2`, and the graph `(X, E_H)` is 2EC. -/
def IsTwoECSub (G : SimpleGraph V) (X : Finset V) (EH : Finset (Sym2 V)) : Prop :=
  (EH : Set (Sym2 V)) ⊆ G.edgeSet ∧ (∀ e ∈ EH, ∀ v ∈ e, v ∈ X) ∧ 2 ≤ X.card ∧
  IsTwoEC ((sg EH).induce (X : Set V))

/-- **β-contractible subgraph.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Definition 6.8, p.26: "For β > 1,
a 2EC subgraph H is β-contractible if every feasible 2ECSS F satisfies |F ∩ E(G[V(H)])| ≥
|E(H)|/β."

**Formalization Note.** `H` is required to be nontrivial (at least two vertices): a one-vertex
subgraph would satisfy the inequality with `0 ≥ 0`, so every graph would contain a contractible
subgraph and the exclusion in the structured class would be empty. `F ∩ E(G[V(H)])` is
`edgesIn F X` since `F ⊆ E(G)`. -/
def IsContractible (G : SimpleGraph V) (β : ℝ) (X : Finset V) (EH : Finset (Sym2 V)) : Prop :=
  IsTwoECSub G X EH ∧ ∀ F, IsTwoECSS G F → (EH.card : ℝ) / β ≤ ((edgesIn F X).card : ℝ)

end TwoConnSS


