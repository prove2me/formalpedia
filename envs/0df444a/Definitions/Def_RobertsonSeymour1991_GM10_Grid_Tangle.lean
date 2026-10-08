-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Grid_Tangle
-- name    : RobertsonSeymour1991_GM10_Grid_Tangle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:17.7222+00:00
-- url     : https://prove2.me/theorems/3e280395-acde-42b5-936d-cc96d3531ba1
-- title:
--   §1, p. 154 — tangle and tangle number
-- statement:
--   A **tangle** $\mathcal T$ of order $\theta\ge1$ in a hypergraph $G$ is a set of separations of order less than $\theta$ satisfying three conditions:
--
--   1. For each separation $(A,B)$ of order less than $\theta$, at least one of $(A,B)$ and $(B,A)$ belongs to $\mathcal T$.
--   2. If three separations $(A_i,B_i)$ belong to $\mathcal T$, then $A_1\cup A_2\cup A_3\ne G$.
--   3. If $(A,B)$ belongs to $\mathcal T$, then $V(A)\ne V(G)$.
--
--   The **tangle number** is the maximum possible order of a tangle, or zero if no tangle exists:
--
--   $$\theta(G)=\max\{\theta:\text{$G$ has a tangle of order $\theta$}\}.$$
--
--   These axioms make the grid construction in (7.3) a genuine tangle, including the vertex condition in the third axiom.
--
--   **Formalization Note** The three selected separations in axiom 2 need not be distinct. The order parameter is part of the predicate. The natural-number supremum used for $\theta(G)$ is zero on the empty set; for finite $G$ its possible orders are bounded by $|V(G)|$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 154, §1, tangle axioms and tangle number

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_Hypergraph

namespace RobertsonSeymour1991.GM10.Grid

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

end RobertsonSeymour1991.GM10.Grid


