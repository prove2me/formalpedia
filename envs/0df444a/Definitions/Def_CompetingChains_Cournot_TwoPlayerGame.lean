-- Prove2me | Definitions.Def_CompetingChains_Cournot_TwoPlayerGame
-- name    : CompetingChains_Cournot_TwoPlayerGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:05.439605+00:00
-- url     : https://prove2.me/theorems/e18c86d2-87a4-4118-a527-f481bb57d4bb
-- title:
--   Pure-strategy Nash equilibrium of a two-player normal-form game
-- statement:
--   Consider a two-player game in normal form. Player 1 chooses a strategy $x_1$ from a set $A_1$, player 2 chooses $x_2$ from a set $A_2$, and $u_1(x_1,x_2)$, $u_2(x_1,x_2)$ are their real payoffs at the profile $(x_1,x_2)$. The profile is a **pure-strategy Nash equilibrium** if neither player can gain by a unilateral deviation:
--
--   $$
--   u_1(y_1,x_2)\le u_1(x_1,x_2)\quad\text{for all } y_1\in A_1,\qquad u_2(x_1,y_2)\le u_2(x_1,x_2)\quad\text{for all } y_2\in A_2 .
--   $$
--
--   The definition also names the set of all such profiles. It is the general game-theoretic notion on which the stage-one information-sharing game of Ha, Tian and Tong (§5.3, Table 1) is built; the paper-specific payoffs are supplied by the setting definition of the mission.
--
--   **Formalization Note** The strategy sets are arbitrary types and the payoffs are real valued; no finiteness is assumed. Only pure strategies are considered.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 21, §5.3 and Table 1 (the stage-one game whose pure equilibria Proposition 7 counts)

import Mathlib

namespace CompetingChains.Cournot

/-- A pure-strategy Nash equilibrium of a two-player game in normal form. Player 1 chooses
`x₁ : A₁`, player 2 chooses `x₂ : A₂`, and `u₁ x₁ x₂`, `u₂ x₁ x₂` are their payoffs at the profile
`(x₁, x₂)`. The profile is an equilibrium when neither player gains by a unilateral deviation. -/
def IsPureNash {A₁ A₂ : Type*} (u₁ u₂ : A₁ → A₂ → ℝ) (x₁ : A₁) (x₂ : A₂) : Prop :=
  (∀ y₁ : A₁, u₁ y₁ x₂ ≤ u₁ x₁ x₂) ∧ (∀ y₂ : A₂, u₂ x₁ y₂ ≤ u₂ x₁ x₂)

/-- The set of pure-strategy Nash equilibria of the two-player game with payoffs `u₁`, `u₂`. -/
def pureNashSet {A₁ A₂ : Type*} (u₁ u₂ : A₁ → A₂ → ℝ) : Set (A₁ × A₂) :=
  {p | IsPureNash u₁ u₂ p.1 p.2}

end CompetingChains.Cournot


