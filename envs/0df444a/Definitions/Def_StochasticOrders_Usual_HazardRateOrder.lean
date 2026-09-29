-- Prove2me | Definitions.Def_StochasticOrders_Usual_HazardRateOrder
-- name    : StochasticOrders_Usual_HazardRateOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:19:08.09535+00:00
-- url     : https://prove2.me/theorems/2d264190-cdbf-40b4-8015-e15ba785dc33
-- title:
--   The hazard rate order (survival-function form)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be real-valued random variables with
--   survival functions $\bar F(x) = P\{X>x\}$ and $\bar G(x) = P\{Y>x\}$. $X$ is said to be
--   **smaller than $Y$ in the hazard rate order**, written $X \le_{hr} Y$, if
--
--   $$\bar F(x)\,\bar G(y) \ge \bar F(y)\,\bar G(x) \quad \text{for all } x \le y.$$
--
--   This is the book's general equivalent condition for the hazard rate order (its more familiar
--   definition, via the hazard rate $r(t) = f(t)/\bar F(t)$ for an absolutely continuous $F$, is a
--   special case of it); it makes sense for arbitrary random variables, not only those with a
--   density. The hazard rate order compares the *conditional* residual-life distributions of $X$
--   and $Y$, and is strictly stronger than the usual stochastic order.
--
--   **Formalization Note** `survival μ X x := μ {ω | x < X ω}` is the `ENNReal`-valued survival
--   function; `HazardRateOrder` states the cross-product inequality directly on `survival`, the
--   form of the definition (Eq. 1.B.4) that needs no absolute-continuity hypothesis.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 16, Eq. (1.B.4)

import Mathlib

namespace StochasticOrders.Usual

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The survival function `P{X > x}` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 16, notation `F̄`). -/
noncomputable def survival (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ENNReal :=
  μ {ω | x < X ω}

/-- The hazard rate order `X ≤hr Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007,
p. 16, Eq. (1.B.4)): the general equivalent condition, valid without assuming absolute
continuity, that the survival functions `F̄` of `X` and `Ḡ` of `Y` satisfy
`F̄(x) Ḡ(y) ≥ F̄(y) Ḡ(x)` for all `x ≤ y`. -/
def HazardRateOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → survival μ X y * survival ν Y x ≤ survival μ X x * survival ν Y y

end StochasticOrders.Usual


