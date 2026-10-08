-- Prove2me | Definitions.Def_MondererShapley_Improvement_IsOrdinalPotential
-- name    : MondererShapley_Improvement_IsOrdinalPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:52.960323+00:00
-- url     : https://prove2.me/theorems/47e32f71-e0a5-4640-9a38-d910944e9ccd
-- title:
--   Ordinal potential, equation (2.1)
-- statement:
--   Let $N$ be a finite player set, $Y^i$ each player's strategy set, $Y=\prod_{i\in N}Y^i$, and $u^i:Y\to\mathbb R$ the payoffs. A function $P:Y\to\mathbb R$ is an **ordinal potential** if every unilateral deviation has the same strict preference ordering under $u^i$ and $P$:
--
--   $$
--   u^i(y^{-i},x)-u^i(y^{-i},z)>0\quad\Longleftrightarrow\quad P(y^{-i},x)-P(y^{-i},z)>0
--   $$
--
--   This is the two-way condition (2.1), stronger than the generalized condition (2.3).
--
--   **Formalization Note** A profile with player $i$'s strategy replaced by $x$ is represented by `Function.update y i x`. The coordinate $y^i$ is ignored.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 127 (PDF p. 4), equation (2.1)

import Mathlib

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Equation (2.1), with `Function.update y i x` representing `(y⁻ⁱ, x)`. -/
def IsOrdinalPotential (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ) : Prop :=
  ∀ (i : ι) (y : ∀ i, Y i) (x z : Y i),
    0 < u i (Function.update y i x) - u i (Function.update y i z) ↔
      0 < P (Function.update y i x) - P (Function.update y i z)

end MondererShapley.Improvement


