-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment
-- name    : WassersteinLinOpt_Ball_HasFinitePthMoment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:14:45.500969+00:00
-- url     : https://prove2.me/theorems/6ab0136a-78b5-4c8b-84d0-9aab2feb560d
-- title:
--   Finite $p$-th moment
-- statement:
--   A Borel measure $\mu$ on a metric space $(X,d)$ has a **finite $p$-th moment** if
--
--   $$\int_X d^p(x,x_0)\,d\mu(x)<\infty\quad\text{for some } x_0\in X.$$
--
--   By the triangle inequality this does not depend on the choice of $x_0$ (p. 1109).
--
--   **Formalization Note.** The integral is the lower Lebesgue integral in `ℝ≥0∞` of `ENNReal.ofReal (dist x x₀ ^ p)`, and "finite" is `< ⊤`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1109, first paragraph of Section 2

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Finite `p`-th moment, p. 1109: `∫_X d^p(x, x₀) dμ(x) < ∞` for some `x₀ ∈ X`. -/
def HasFinitePthMoment {X : Type*} [MetricSpace X] [MeasurableSpace X] (p : ℝ)
    (μ : Measure X) : Prop :=
  ∃ x₀ : X, ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂μ < ⊤

end WassersteinLinOpt.Ball


