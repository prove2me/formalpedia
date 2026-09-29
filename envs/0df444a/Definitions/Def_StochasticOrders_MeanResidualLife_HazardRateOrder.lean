-- Prove2me | Definitions.Def_StochasticOrders_MeanResidualLife_HazardRateOrder
-- name    : StochasticOrders_MeanResidualLife_HazardRateOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:24:34.404001+00:00
-- url     : https://prove2.me/theorems/60a66e8d-34ba-424d-b163-9d0a0bb07734
-- title:
--   The hazard rate order (survival-function form), restated locally
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be random variables with survival
--   functions $\bar F(x) = P\{X>x\}$ and $\bar G(x) = P\{Y>x\}$. $X$ is said to be **smaller than
--   $Y$ in the hazard rate order**, written $X \le_{hr} Y$, if
--
--   $$\bar F(x)\,\bar G(y) \ge \bar F(y)\,\bar G(x) \quad \text{for all } x \le y.$$
--
--   This is the same general, absolute-continuity-free form of the hazard rate order used in
--   Chunk 01 of this series; it is restated in this mission's own namespace because a draft
--   mission cannot import another draft's Lean.
--
--   **Formalization Note** Identical in shape to `StochasticOrders.Usual.HazardRateOrder`, with
--   its own local `survival` helper.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 16, Eq. (1.B.4)

import Mathlib

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The survival function `P{X > x}` of a random variable `X` on `(Ω, μ)` (Shaked & Shanthikumar,
*Stochastic Orders*, Springer 2007, p. 16, notation `F̄`), restated locally since this chapter's
mission cannot import Chunk 01's `Definitions.Def_StochasticOrders_Usual_HazardRateOrder`. -/
noncomputable def survival (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ENNReal :=
  μ {ω | x < X ω}

/-- The hazard rate order `X ≤hr Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007,
p. 16, Eq. (1.B.4)), restated locally (see `survival` above): the general equivalent condition,
valid without assuming absolute continuity, that the survival functions `F̄` of `X` and `Ḡ` of `Y`
satisfy `F̄(x) Ḡ(y) ≥ F̄(y) Ḡ(x)` for all `x ≤ y`. -/
def HazardRateOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → survival μ X y * survival ν Y x ≤ survival μ X x * survival ν Y y

end StochasticOrders.MeanResidualLife


