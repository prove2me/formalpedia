-- Prove2me | Definitions.Def_PubFrequency_MixedEquilibrium
-- name    : PubFrequency_MixedEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:53.305317+00:00
-- url     : https://prove2.me/theorems/5c422a28-9a83-40e5-a77f-a10541f14fd5
-- title:
--   Pure and mixed Nash equilibria (with equilibrium profits) of a two-player game with real actions, display (9)
-- statement:
--   This module defines the two equilibrium notions used for the pricing game of Chen and Roels, for an arbitrary two-player game whose actions are real numbers (prices). Player 1's payoff is $f_1(x,y)$ when it plays $x$ and player 2 plays $y$; player 2's payoff is $f_2(y,x)$ (own action first).
--
--   1. **Pure-strategy Nash equilibrium.** A pair $(x,y)\in\mathbb R^2$ such that $f_1(x',y)\le f_1(x,y)$ for every $x'\in\mathbb R$ and $f_2(y',x)\le f_2(y,x)$ for every $y'\in\mathbb R$.
--   2. **Mixed-strategy Nash equilibrium with profits $(P_1,P_2)$** (display (9), p. 12). There are probability measures $\mu_1,\mu_2$ on $\mathbb R$, sets $S_1,S_2\subseteq\mathbb R$ and a bound $B$ such that, for $i\in\{1,2\}$ and $-i$ the other player:
--      - $\mu_i(S_i^{\mathrm c})=0$ and $\mu_i(\mathbb R\setminus[-B,B])=0$;
--      - for every action $x$, the payoff $y\mapsto f_i(x,y)$ is $\mu_{-i}$-integrable;
--      - $\int f_i(x,y)\,\mu_{-i}(dy)=P_i$ for every $x\in S_i$, and $\int f_i(x,y)\,\mu_{-i}(dy)\le P_i$ for every $x\notin S_i$.
--
--   This is the paper's definition "$\forall r_i\in S_i$, $\Pi_i(r_i;F_{-i}(\cdot),\mathbf u)=\Pi^*_i(\mathbf u)$; $\forall r_i\notin S_i$, $\Pi_i(r_i;F_{-i}(\cdot),\mathbf u)\le\Pi^*_i(\mathbf u)$", with each pricing cdf $F_i$ represented by its law $\mu_i$. Since $\mu_i$ is a probability measure carried by $S_i$, $P_i$ is player $i$'s expected payoff at the mixed profile and no pure deviation earns more, so $(\mu_1,\mu_2)$ is a Nash equilibrium in mixed strategies.
--
--   **Formalization Note** Integrability is part of the definition, because Lean assigns the value $0$ to the integral of a non-integrable function. Strategies are required to have bounded support (the paper's equilibrium distributions do). Deviations range over all real actions, with no sign constraint, as in the paper.
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), §3.3, p.11 (pure equilibrium) and eq. (9), p.12 (PDF 12–13)

import Mathlib

open MeasureTheory

namespace PubFrequency

/-- **Pure-strategy Nash equilibrium of a two-player game with real actions.** `f₁ x y` is
player 1's payoff when it plays `x` and player 2 plays `y`; `f₂ y x` is player 2's payoff when
it plays `y` and player 1 plays `x`. The pair `(x, y)` is a pure equilibrium if no player gains by
a unilateral deviation to any real action.

Chen–Roels, *Fast or Slow? Competing on Publication Frequency*, SSRN 3986163
(INSEAD WP 2021/74/TOM), §3.3, p. 11 (PDF 12) ("pure-strategy Nash equilibrium in the pricing
game"). -/
def IsPureEq (f₁ f₂ : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  (∀ x' : ℝ, f₁ x' y ≤ f₁ x y) ∧ (∀ y' : ℝ, f₂ y' x ≤ f₂ y x)

/-- **Mixed-strategy Nash equilibrium with equilibrium profits `(P₁, P₂)`** of a two-player game
with real actions, in the form of display (9) of Chen–Roels, *Fast or Slow? Competing on
Publication Frequency*, SSRN 3986163 (INSEAD WP 2021/74/TOM), §3.3, p. 12 (PDF 13).
Payoffs are as in `IsPureEq`: `f₁ x y` for player 1, `f₂ y x` for player 2.

There are probability measures `μ₁, μ₂` on `ℝ` (the mixed strategies), sets `S₁, S₂` and a bound
`B` such that, for each player `i`:
* `μᵢ (Sᵢᶜ) = 0` (`Sᵢ` carries the strategy) and `μᵢ` is concentrated on `[-B, B]`;
* for every own action `x`, the payoff `y ↦ fᵢ x y` is integrable against the rival's strategy;
* every `x ∈ Sᵢ` earns exactly `Pᵢ` in expectation against the rival's strategy;
* every `x ∉ Sᵢ` earns at most `Pᵢ`.

This is the paper's "∀ri ∈ Si, Πi(ri;F−i(·),u) = Π∗i(u); ∀ri ∉ Si, Πi(ri;F−i(·),u) ≤ Π∗i(u)",
with the cdf `F_{−i}` represented by its law `μ_{−i}`.

**Formalization Note.** Integrability is part of the definition: Lean's Bochner integral of a
non-integrable function is `0`, which would otherwise let junk integrals satisfy the conditions.
The bounded support (`[-B, B]`) is required of the strategies; the paper's equilibrium
distributions are bounded. Deviations range over all real actions, with no sign constraint.
Since `μᵢ` is a probability measure with `μᵢ (Sᵢᶜ) = 0`, `Sᵢ` is nonempty, and `Pᵢ` is player
`i`'s expected payoff at the profile `(μ₁, μ₂)`. -/
def IsMixedEqWithProfits (f₁ f₂ : ℝ → ℝ → ℝ) (P₁ P₂ : ℝ) : Prop :=
  ∃ (μ₁ μ₂ : Measure ℝ) (S₁ S₂ : Set ℝ) (B : ℝ),
    IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
    μ₁ S₁ᶜ = 0 ∧ μ₂ S₂ᶜ = 0 ∧
    μ₁ (Set.Icc (-B) B)ᶜ = 0 ∧ μ₂ (Set.Icc (-B) B)ᶜ = 0 ∧
    (∀ x : ℝ, Integrable (fun y => f₁ x y) μ₂) ∧
    (∀ y : ℝ, Integrable (fun x => f₂ y x) μ₁) ∧
    (∀ x ∈ S₁, ∫ y, f₁ x y ∂μ₂ = P₁) ∧ (∀ x ∉ S₁, ∫ y, f₁ x y ∂μ₂ ≤ P₁) ∧
    (∀ y ∈ S₂, ∫ x, f₂ y x ∂μ₁ = P₂) ∧ (∀ y ∉ S₂, ∫ x, f₂ y x ∂μ₁ ≤ P₂)

end PubFrequency


