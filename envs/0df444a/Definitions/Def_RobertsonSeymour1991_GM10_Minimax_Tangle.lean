-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle
-- name    : RobertsonSeymour1991_GM10_Minimax_Tangle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:24.542256+00:00
-- url     : https://prove2.me/theorems/cdab6e3f-7f5f-4c40-b1c4-1e0eaf1f217d
-- title:
--   §1, p. 154 and §2, p. 157 — tangle of order θ, tangle number θ(G), extreme separation
-- statement:
--   Let $G$ be a hypergraph and $\theta\ge1$ an integer. A **tangle in $G$ of order $\theta$** is a set $\mathcal T$ of separations of $G$, each of order $<\theta$, such that
--
--   1. for every separation $(A,B)$ of $G$ of order $<\theta$, one of $(A,B)$, $(B,A)$ is in $\mathcal T$;
--   2. if $(A_1,B_1),(A_2,B_2),(A_3,B_3)\in\mathcal T$ then $A_1\cup A_2\cup A_3\ne G$;
--   3. if $(A,B)\in\mathcal T$ then $V(A)\ne V(G)$.
--
--   The **tangle number** $\theta(G)$ is the maximum order of a tangle in $G$, or $0$ if $G$ has no tangle. A separation $(A,B)\in\mathcal T$ is **extreme** if $A'=A$ and $B'=B$ for every $(A',B')\in\mathcal T$ with $A\subseteq A'$ and $B'\subseteq B$.
--
--   Tangles are the obstruction side of the minimax theorem of this mission: a tangle of large order certifies that $G$ has no branch-decomposition of small width.
--
--   **Formalization Note** The order $\theta$ is a parameter of the predicate, and $\theta\ge1$ is part of it. The three separations in the second axiom need not be distinct. $\theta(G)$ is `sSup` of the set of orders of tangles in $\mathbb N$; every tangle has order at most $|V(G)|$ (p. 154), so the set is bounded and the supremum is the maximum, and the empty set gives $0$ as the paper prescribes.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 154 (tangle, tangle number), p. 157 (extreme)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph

namespace RobertsonSeymour1991.GM10.Minimax

variable {V E : Type}

namespace Hypergraph

/-- p. 154: `𝒯` is a tangle in `G` of order `θ`. -/
def IsTangle (G : Hypergraph V E) (θ : ℕ) (𝒯 : Set (G.Sub × G.Sub)) : Prop :=
  1 ≤ θ ∧
  (∀ p ∈ 𝒯, IsSeparation p.1 p.2 ∧ order p.1 p.2 < θ) ∧
  (∀ A B : G.Sub, IsSeparation A B → order A B < θ → (A, B) ∈ 𝒯 ∨ (B, A) ∈ 𝒯) ∧
  (∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, ∀ p₃ ∈ 𝒯, (p₁.1.union p₂.1).union p₃.1 ≠ Sub.top G) ∧
  (∀ p ∈ 𝒯, p.1.verts ≠ Set.univ)

/-- p. 154: the tangle number `θ(G)`, the maximum order of a tangle in `G` (`0` if there is none). -/
noncomputable def tangleNumber (G : Hypergraph V E) : ℕ := sSup {θ | ∃ 𝒯, IsTangle G θ 𝒯}

/-- p. 157: a separation `(A, B) ∈ 𝒯` is extreme if `A' = A` and `B' = B` for every `(A', B') ∈ 𝒯`
with `A ⊆ A'` and `B' ⊆ B`. -/
def IsExtreme {G : Hypergraph V E} (𝒯 : Set (G.Sub × G.Sub)) (A B : G.Sub) : Prop :=
  (A, B) ∈ 𝒯 ∧ ∀ A' B' : G.Sub, (A', B') ∈ 𝒯 → A.le A' → B'.le B → A' = A ∧ B' = B

end Hypergraph

end RobertsonSeymour1991.GM10.Minimax


