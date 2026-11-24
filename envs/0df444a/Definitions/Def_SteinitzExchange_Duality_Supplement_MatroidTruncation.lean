-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_MatroidTruncation
-- name    : SteinitzExchange_Duality_Supplement_MatroidTruncation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:26:55.185857+00:00
-- url     : https://prove2.me/theorems/a83a5f59-a8e2-4686-947a-40565af9c477
-- title:
--   Matroid truncation $\mathcal B_k$ and truncated valuation $\omega_k$
-- statement:
--   Let $\mathbf M=(E,\mathcal B)$ be a matroid with a function $\omega:\mathcal B\to\mathbb R$, and let $k\ge 0$ be an integer. The **truncation** of $\mathbf M$ to rank $k$ is $\mathbf M_k=(E,\mathcal B_k)$ with
--   $$\mathcal B_k=\{X\subseteq E\mid |X|=k,\ \exists B:\ X\subseteq B\in\mathcal B\},$$
--   and $\omega_k:\mathcal B_k\to\mathbb R$ is
--   $$\omega_k(X)=\max\{\omega(B)\mid X\subseteq B\in\mathcal B\}\qquad(X\in\mathcal B_k).$$
--   The **rank** of $\mathbf M$ is the common cardinality of its bases.
--
--   **Formalization Note.** `matroidRank ℬ` is the largest cardinality of a member of $\mathcal B$, which for a matroid is the common base cardinality. `truncValue` is a real `⨆` over the finite set of bases containing $X$: the paper's maximum for $X\in\mathcal B_k$, and the junk value $0$ when no base contains $X$ (never used).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 306, Section 7.1 (definition of M_k and ω_k)

import Mathlib

namespace SteinitzExchange.Duality.Supplement

/-- The rank of a matroid given by its base family: the largest base cardinality (all bases of
a matroid have the same cardinality, so this is the common one). -/
def matroidRank {E : Type*} (ℬ : Finset (Finset E)) : ℕ :=
  ℬ.sup Finset.card

/-- The base family of the truncation `M_k` (Murota 1996, p. 306):
`ℬ_k = {X ⊆ E | |X| = k, ∃ B : X ⊆ B ∈ ℬ}`. -/
noncomputable def truncBases {E : Type*} [Fintype E] (ℬ : Finset (Finset E)) (k : ℕ) :
    Finset (Finset E) := by
  classical
  exact Finset.univ.filter (fun X => X.card = k ∧ ∃ B ∈ ℬ, X ⊆ B)

/-- `ω_k(X) = max{ω(B) | X ⊆ B ∈ ℬ}` for `X ∈ ℬ_k` (Murota 1996, p. 306). For `X ∈ ℬ_k` the
family is finite and nonempty, so the real supremum is the maximum; if no base contains `X`
the value is the junk value `0`, never used. -/
noncomputable def truncValue {E : Type*} (ℬ : Finset (Finset E)) (ω : Finset E → ℝ)
    (X : Finset E) : ℝ :=
  ⨆ B : {B : Finset E // B ∈ ℬ ∧ X ⊆ B}, ω B.1

end SteinitzExchange.Duality.Supplement


