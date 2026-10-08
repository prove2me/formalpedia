-- Prove2me | Definitions.Def_MondererShapley_ClosedPath_IsPotential
-- name    : MondererShapley_ClosedPath_IsPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:57.348334+00:00
-- url     : https://prove2.me/theorems/826e6e20-a8b0-4667-aed4-26b946f94b91
-- title:
--   Exact potential of a strategic-form game
-- statement:
--   For a game with finitely many players, let $Y^i$ be player $i$'s strategy set, $Y$ the set of profiles, and $u^i:Y\to\mathbb R$ the payoff of player $i$. A function $P:Y\to\mathbb R$ is an **exact potential** when every unilateral payoff difference equals the corresponding difference of $P$:
--
--   $$u^i(y^{-i},x)-u^i(y^{-i},z)=P(y^{-i},x)-P(y^{-i},z)$$
--
--   for every player $i$, opponents' profile $y^{-i}$, and $x,z\in Y^i$. This is the unit-weight case of equation (2.2) and supplies the common notion used by Theorem 2.8 and Lemma 2.7.
--
--   **Formalization Note** Players form a finite type; their strategy sets need not be finite. Updating coordinate $i$ of a complete profile represents $(y^{-i},x)$.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 127 (PDF p. 4), Eq. (2.2), and p. 128 (PDF p. 5), exact-potential definition; https://doi.org/10.1006/game.1996.0044

import Mathlib

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Exact potential of a strategic-form game, Monderer--Shapley (2.2) with all weights one. -/
def IsPotential (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ) : Prop :=
  ∀ (i : ι) (y : ∀ i, Y i) (x z : Y i),
    u i (Function.update y i x) - u i (Function.update y i z) =
      P (Function.update y i x) - P (Function.update y i z)

end MondererShapley.ClosedPath


