-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_MatchingInduction
-- name    : SteinitzExchange_Duality_Supplement_MatchingInduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:26:25.118895+00:00
-- url     : https://prove2.me/theorems/52fa6a79-0ad9-44b3-94bc-89691c70ff1e
-- title:
--   Matching-induced base family $\tilde{\mathcal B}$ and valuation $\tilde\omega$ (7.7)
-- statement:
--   Let $G=(V^+,V^-,A)$ be a bipartite graph with finite arc set $A$ (each arc joins an entrance vertex in $V^+$ to an exit vertex in $V^-$; parallel arcs are allowed), $w:A\to\mathbb R$ a weight function, and $\mathcal B^+\subseteq 2^{V^+}$ with $\omega^+:\mathcal B^+\to\mathbb R$. A **matching** is a set $M\subseteq A$ of arcs no two of which share an endpoint; $\partial^+M\subseteq V^+$ and $\partial^-M\subseteq V^-$ are the sets of entrance and exit vertices incident to $M$, and $w(M)=\sum_{a\in M}w(a)$. Define
--   $$\tilde{\mathcal B}=\{\partial^-M\mid M\ \text{a matching with}\ \partial^+M\in\mathcal B^+\},$$
--   $$\tilde\omega(X)=\max\{w(M)+\omega^+(\partial^+M)\mid M\ \text{matching},\ \partial^+M\in\mathcal B^+,\ \partial^-M=X\}\qquad(X\in\tilde{\mathcal B}).$$
--
--   Theorem 7.3 of the paper shows that $\tilde\omega$ is a valuation of $(V^-,\tilde{\mathcal B})$ when $(V^+,\mathcal B^+)$ is a matroid with valuation $\omega^+$.
--
--   **Formalization Note.** The two sides are types `P` ($V^+$) and `Q` ($V^-$), and arcs a finite type with endpoint maps `src : A → P`, `dst : A → Q`; a matching is a finset of arcs on which both maps are injective. `matchingValue` is a real `⨆` over the finite set of admissible matchings with $\partial^-M=X$: the paper's maximum for $X\in\tilde{\mathcal B}$, and the junk value $0$ (empty family) off $\tilde{\mathcal B}$, where it is never used.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 305–306, Section 7.1, Eq. (7.7)

import Mathlib

namespace SteinitzExchange.Duality.Supplement

/-! Matching induction (Murota 1996, pp. 305–306, Eq. (7.7)). The bipartite graph
`G = (V⁺, V⁻, A)` has vertex types `P` (= `V⁺`) and `Q` (= `V⁻`) and a finite arc type `A` with
endpoint maps `src : A → P`, `dst : A → Q` (parallel arcs allowed). -/

/-- `M ⊆ A` is a matching: no two arcs of `M` share an endpoint. -/
def IsMatching {P Q A : Type*} (src : A → P) (dst : A → Q) (M : Finset A) : Prop :=
  Set.InjOn src (M : Set A) ∧ Set.InjOn dst (M : Set A)

/-- `∂⁺M ⊆ V⁺`: the entrance vertices incident to `M`. -/
def plusBd {P A : Type*} [DecidableEq P] (src : A → P) (M : Finset A) : Finset P :=
  M.image src

/-- `∂⁻M ⊆ V⁻`: the exit vertices incident to `M`. -/
def minusBd {Q A : Type*} [DecidableEq Q] (dst : A → Q) (M : Finset A) : Finset Q :=
  M.image dst

/-- `w(M) = Σ_{a ∈ M} w(a)`. -/
def matchingWeight {A : Type*} (w : A → ℝ) (M : Finset A) : ℝ :=
  ∑ a ∈ M, w a

/-- The matchings `M` with `∂⁺M ∈ ℬ⁺`. -/
noncomputable def admissibleMatchings {P Q A : Type*} [Fintype A] [DecidableEq P]
    (src : A → P) (dst : A → Q) (ℬp : Finset (Finset P)) : Finset (Finset A) := by
  classical
  exact Finset.univ.filter (fun M => IsMatching src dst M ∧ plusBd src M ∈ ℬp)

/-- `ℬ̃ = {∂⁻M | M a matching with ∂⁺M ∈ ℬ⁺}` (Murota 1996, p. 305). -/
noncomputable def matchingBase {P Q A : Type*} [Fintype A] [DecidableEq P] [DecidableEq Q]
    (src : A → P) (dst : A → Q) (ℬp : Finset (Finset P)) : Finset (Finset Q) :=
  (admissibleMatchings src dst ℬp).image (minusBd dst)

/-- `ω̃(X) = max{w(M) + ω⁺(∂⁺M) | M matching, ∂⁺M ∈ ℬ⁺, ∂⁻M = X}` for `X ∈ ℬ̃` (Eq. (7.7)).
For `X ∈ ℬ̃` the family is finite and nonempty, so the real supremum is the maximum; for
`X ∉ ℬ̃` it is empty and the value is the junk value `0`, never used. -/
noncomputable def matchingValue {P Q A : Type*} [Fintype A] [DecidableEq P] [DecidableEq Q]
    (src : A → P) (dst : A → Q) (w : A → ℝ) (ℬp : Finset (Finset P)) (ωp : Finset P → ℝ)
    (X : Finset Q) : ℝ :=
  ⨆ M : {M : Finset A // M ∈ admissibleMatchings src dst ℬp ∧ minusBd dst M = X},
    matchingWeight w M.1 + ωp (plusBd src M.1)

end SteinitzExchange.Duality.Supplement


