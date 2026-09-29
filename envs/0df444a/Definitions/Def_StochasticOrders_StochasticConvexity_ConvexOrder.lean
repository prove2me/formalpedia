-- Prove2me | Definitions.Def_StochasticOrders_StochasticConvexity_ConvexOrder
-- name    : StochasticOrders_StochasticConvexity_ConvexOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:32.648254+00:00
-- url     : https://prove2.me/theorems/682ebd24-4360-4d5f-bff5-09daa165812d
-- title:
--   The (univariate) convex order, restated locally
-- statement:
--   Let $X$ be a random variable on a probability space $(\Omega,\mu)$ and let $Y$ be a random
--   variable on a (possibly different) probability space $(\Omega',\nu)$. $X$ is said to be
--   **smaller than $Y$ in the convex order**, written $X \le_{cx} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every convex }
--     \varphi:\mathbb{R}\to\mathbb{R} \text{ for which the two expectations exist.}$$
--
--   This is the same univariate convex order Chunk 03 (`StochasticOrders.Convex`) defines,
--   restated here because drafts cannot import another mission's definitions. It is used by
--   Theorem 8.A.13(b) to compare the *number of terms* `M`, `N` of a random sum.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, Chapter 3, Eq. (3.A.1) (restated locally)

import Mathlib

namespace StochasticOrders.StochasticConvexity

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The (univariate) convex order `X ≤cx Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, restated locally from Chapter 3's Eq. (3.A.1), the same shape this series' Chunk 03 uses):
a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y` on a (possibly different)
probability space `(Ω', ν)` in the convex order if `E[φ(X)] ≤ E[φ(Y)]` for every convex function
`φ : ℝ → ℝ` for which the two expectations exist. Restated here, rather than imported, since
drafts cannot import another mission's definitions. -/
def ConvexOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

end StochasticOrders.StochasticConvexity


