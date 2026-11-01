-- Prove2me | Definitions.Def_DivQuotient_DQ
-- name    : DivQuotient_DQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:06.831129+00:00
-- url     : https://prove2.me/theorems/cb0ef7ab-1b5c-4bfe-9e57-90df2b2f6172
-- title:
--   Diversification quotient $\mathrm{DQ}^\rho_\alpha$ (Definition 1, eq. (3))
-- statement:
--   Let $\bar\alpha\in(0,\infty]$, $I=(0,\bar\alpha)$, and let $\rho=(\rho_\beta)_{\beta\in I}$ be a class of risk measures that is **decreasing**: $\rho_\gamma(X)\le\rho_\beta(X)$ whenever $\beta\le\gamma$ in $I$. For $\alpha\in I$ and $\mathbf X\in\mathcal X^n$, the **diversification quotient** is
--
--   $$
--   \mathrm{DQ}^\rho_\alpha(\mathbf X)=\frac{\alpha^*}{\alpha},\qquad \alpha^*=\inf\Big\{\beta\in I:\ \rho_\beta\Big(\sum_{i=1}^nX_i\Big)\le\sum_{i=1}^n\rho_\alpha(X_i)\Big\},
--   $$
--
--   with the convention $\inf\varnothing=\bar\alpha$.
--
--   DQ compares the risk of the pooled portfolio with the sum of the individual risks on the scale of the parameter $\beta$: it is the smallest relative level at which pooling does not increase risk.
--
--   **Formalization Note** $\bar\alpha$ is an `EReal` (so $\bar\alpha=\infty$ is allowed). A class is a map `ℝ → Lp ℝ ⊤ P → EReal`, of which only the members indexed by $I$ matter; a real-valued class is coerced. $\alpha^*$ is the `EReal` infimum, capped by $\bar\alpha$; the cap only acts on the empty set. The quotient is `EReal` division by the real $\alpha>0$, which sends $+\infty$ to $+\infty$.
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Definition 1 and eq. (3), pp.9–10

import Mathlib
import Definitions.Def_DivQuotient_Axioms

open MeasureTheory

namespace DivQuotient

/-! The diversification quotient, Definition 1 and eq. (3), arXiv:2206.13679v6, pp.9–10. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The index interval `I = (0, ᾱ)` of Definition 1 (arXiv:2206.13679v6, p.9), with
`ᾱ ∈ (0, ∞]` given as an `EReal`; `ᾱ = ⊤` gives `I = (0, ∞)`. -/
def IndexSet (abar : EReal) : Set ℝ :=
  {β : ℝ | 0 < β ∧ (β : EReal) < abar}

/-- A **decreasing class** `ρ = (ρ_β)_{β∈I}` (arXiv:2206.13679v6, p.9): `ρ_γ(X) ≤ ρ_β(X)` for
`β ≤ γ` in `I` ("decreasing" is non-strict, p.4).

**Formalization Note.** A class is a map `ρ : ℝ → Lp ℝ ⊤ P → EReal`; only its members with
index in `I` matter. A real-valued class is coerced, `fun β X => (ρ β X : EReal)`. -/
def IsDecreasingClass (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → EReal) : Prop :=
  ∀ β ∈ IndexSet abar, ∀ γ ∈ IndexSet abar, β ≤ γ → ∀ X, ρ γ X ≤ ρ β X

/-- The level `α* = inf{β ∈ I : ρ_β(∑ Xᵢ) ≤ ∑ ρ_α(Xᵢ)}` of eq. (3), arXiv:2206.13679v6, p.10,
with the convention `inf ∅ = ᾱ`.

**Formalization Note.** The infimum is taken in `EReal` (`⨅`, which is `⊤` on the empty set)
and then capped by `ᾱ`. Every `β ∈ I` is `< ᾱ`, so the cap changes the value only when the set
is empty, where it gives `ᾱ` as the page requires. The sum `∑ ρ_α(Xᵢ)` is an `EReal` sum; in
every statement of the mission `ρ_α` is real valued. -/
noncomputable def alphaStar (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → EReal) (α : ℝ)
    (X : Fin n → Lp ℝ ⊤ P) : EReal :=
  min abar (⨅ β ∈ {β : ℝ | β ∈ IndexSet abar ∧ ρ β (S X) ≤ ∑ i, ρ α (X i)}, (β : EReal))

/-- **Diversification quotient** `DQ^ρ_α(X) = α*/α` (Definition 1, eq. (3),
arXiv:2206.13679v6, pp.9–10), for a class `ρ` indexed by `I = (0, ᾱ)` and a level `α ∈ I`.

**Formalization Note.** The quotient is `EReal` division by the positive real `α`; it sends
`⊤` to `⊤`. -/
noncomputable def DQ (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → EReal) (α : ℝ) :
    (Fin n → Lp ℝ ⊤ P) → EReal :=
  fun X => alphaStar abar ρ α X / (α : EReal)

end DivQuotient


