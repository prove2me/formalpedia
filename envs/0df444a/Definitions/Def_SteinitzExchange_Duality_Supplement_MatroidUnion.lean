-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_MatroidUnion
-- name    : SteinitzExchange_Duality_Supplement_MatroidUnion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:26:38.981522+00:00
-- url     : https://prove2.me/theorems/6537554b-54c3-4153-8e0f-bc418878c058
-- title:
--   Matroid union $\mathcal B_1\vee\mathcal B_2$ and union valuation $\omega_1\vee\omega_2$
-- statement:
--   Let $\mathcal B_1,\mathcal B_2\subseteq 2^E$ be base families of matroids $\mathbf M_1=(E,\mathcal B_1)$, $\mathbf M_2=(E,\mathcal B_2)$ with functions $\omega_1:\mathcal B_1\to\mathbb R$, $\omega_2:\mathcal B_2\to\mathbb R$. The union $\mathbf M_1\vee\mathbf M_2=(E,\mathcal B_1\vee\mathcal B_2)$ has as base family $\mathcal B_1\vee\mathcal B_2$ the family of **inclusion-maximal** elements of
--   $$\{X_1\cup X_2\mid X_1\in\mathcal B_1,\ X_2\in\mathcal B_2\},$$
--   and
--   $$(\omega_1\vee\omega_2)(X)=\max\{\omega_1(X_1)+\omega_2(X_2)\mid X_1\cup X_2=X,\ X_1\in\mathcal B_1,\ X_2\in\mathcal B_2\}\qquad(X\in\mathcal B_1\vee\mathcal B_2).$$
--   All pairs with union $X$ are admitted; they need not be disjoint.
--
--   **Formalization Note.** `unionBases` filters the finite family of unions $X_1\cup X_2$ to its inclusion-maximal members. `unionValue` is a real `⨆` over the finite set of pairs $(X_1,X_2)\in\mathcal B_1\times\mathcal B_2$ with $X_1\cup X_2=X$: the paper's maximum for $X\in\mathcal B_1\vee\mathcal B_2$, and the junk value $0$ when no pair has union $X$ (never used).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 306, Section 7.1 (definition of M₁ ∨ M₂ and ω₁ ∨ ω₂)

import Mathlib

namespace SteinitzExchange.Duality.Supplement

/-- `{X₁ ∪ X₂ | X₁ ∈ ℬ₁, X₂ ∈ ℬ₂}` (Murota 1996, p. 306). -/
def unionCandidates {E : Type*} [DecidableEq E] (ℬ₁ ℬ₂ : Finset (Finset E)) :
    Finset (Finset E) :=
  (ℬ₁ ×ˢ ℬ₂).image (fun q => q.1 ∪ q.2)

/-- `ℬ₁ ∨ ℬ₂`: the inclusion-maximal elements of `{X₁ ∪ X₂ | X₁ ∈ ℬ₁, X₂ ∈ ℬ₂}`, the base
family of the union `M₁ ∨ M₂` (Murota 1996, p. 306). -/
noncomputable def unionBases {E : Type*} [DecidableEq E] (ℬ₁ ℬ₂ : Finset (Finset E)) :
    Finset (Finset E) := by
  classical
  exact (unionCandidates ℬ₁ ℬ₂).filter
    (fun X => ∀ Y ∈ unionCandidates ℬ₁ ℬ₂, X ⊆ Y → Y = X)

/-- `(ω₁ ∨ ω₂)(X) = max{ω₁(X₁) + ω₂(X₂) | X₁ ∪ X₂ = X, X₁ ∈ ℬ₁, X₂ ∈ ℬ₂}` for
`X ∈ ℬ₁ ∨ ℬ₂` (Murota 1996, p. 306). All pairs with union `X` are admitted (they need not be
disjoint). For such `X` the family is finite and nonempty, so the real supremum is the maximum;
off the union family it may be empty, with junk value `0`, never used. -/
noncomputable def unionValue {E : Type*} [DecidableEq E] (ℬ₁ : Finset (Finset E))
    (ω₁ : Finset E → ℝ) (ℬ₂ : Finset (Finset E)) (ω₂ : Finset E → ℝ) (X : Finset E) : ℝ :=
  ⨆ q : {q : Finset E × Finset E // q.1 ∈ ℬ₁ ∧ q.2 ∈ ℬ₂ ∧ q.1 ∪ q.2 = X},
    ω₁ q.1.1 + ω₂ q.1.2

end SteinitzExchange.Duality.Supplement


