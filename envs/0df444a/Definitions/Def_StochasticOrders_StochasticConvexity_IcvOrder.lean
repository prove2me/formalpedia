-- Prove2me | Definitions.Def_StochasticOrders_StochasticConvexity_IcvOrder
-- name    : StochasticOrders_StochasticConvexity_IcvOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:14:28.920985+00:00
-- url     : https://prove2.me/theorems/78b32017-9843-4209-af81-842faa98bdd9
-- title:
--   The (univariate) increasing concave order, restated locally
-- statement:
--   Let $X$ and $Y$ be random variables, on probability spaces $(\Omega,\mu)$ and
--   $(\Omega',\nu)$ respectively. $X$ is said to be **smaller than $Y$ in the increasing concave
--   order**, written $X \le_{icv} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every increasing concave }
--     \varphi:\mathbb{R}\to\mathbb{R} \text{ for which the two expectations exist.}$$
--
--   This is the same univariate increasing concave order Chunk 04
--   (`StochasticOrders.MonotoneConvex`) defines, restated here because drafts cannot import
--   another mission's definitions. Used by Theorem 8.A.13(a)'s bracketed `≤icv` case.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, Chapter 4, Eq. (4.A.1) (restated locally)

import Mathlib

namespace StochasticOrders.StochasticConvexity

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The (univariate) increasing concave order `X ≤icv Y` (Shaked & Shanthikumar, *Stochastic
Orders*, Springer 2007, restated locally from Chapter 4's Eq. (4.A.1), the same shape this
series' Chunk 04 uses): a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y`
on a (possibly different) probability space `(Ω', ν)` in the increasing concave order if
`E[φ(X)] ≤ E[φ(Y)]` for every increasing concave function `φ : ℝ → ℝ` for which the two
expectations exist. Restated here, rather than imported, since drafts cannot import another
mission's definitions. -/
def IcvOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConcaveOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

end StochasticOrders.StochasticConvexity


