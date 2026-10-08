-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Tangle
-- name    : RobertsonSeymour1991_GM10_TreeWidth_Tangle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:15:57.708364+00:00
-- url     : https://prove2.me/theorems/fa6f631d-ece3-48d8-b775-1d315ef22aab
-- title:
--   §1, p. 154 — tangle of order θ and the tangle number θ(G)
-- statement:
--   Let $G$ be a hypergraph and $\theta \ge 1$ an integer. A **tangle in $G$ of order $\theta$** is a set $\mathcal T$ of separations of $G$, each of order $< \theta$, such that
--
--   1. for every separation $(A, B)$ of $G$ of order $< \theta$, one of $(A, B)$, $(B, A)$ is in $\mathcal T$;
--   2. if $(A_1, B_1), (A_2, B_2), (A_3, B_3) \in \mathcal T$ then $A_1 \cup A_2 \cup A_3 \neq G$;
--   3. if $(A, B) \in \mathcal T$ then $V(A) \neq V(G)$.
--
--   The **tangle number** $\theta(G)$ is the maximum order of a tangle in $G$, or $0$ if there are no tangles.
--
--   Tangles are the obstruction to small tree-decompositions studied in Graph Minors X; here they are needed only for the companion statement (5.2).
--
--   **Formalization Note** In the second axiom the three separations need not be distinct, as in the paper. The tangle number is the `sSup` in $\mathbb N$ of the set of orders of tangles; this set is bounded (every tangle has order at most $|V(G)|$, p. 154), so the `sSup` is the maximum, and the empty set gives $0$ as the paper stipulates.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 154 (tangle, tangle axioms, tangle number)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph

namespace RobertsonSeymour1991.GM10.TreeWidth

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

end Hypergraph

end RobertsonSeymour1991.GM10.TreeWidth


