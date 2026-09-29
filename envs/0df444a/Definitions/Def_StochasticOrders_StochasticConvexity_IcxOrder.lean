-- Prove2me | Definitions.Def_StochasticOrders_StochasticConvexity_IcxOrder
-- name    : StochasticOrders_StochasticConvexity_IcxOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:55.260255+00:00
-- url     : https://prove2.me/theorems/93ae506f-f832-47dc-8d22-70311263dd5f
-- title:
--   The (univariate) increasing convex order, restated locally
-- statement:
--   Let $X$ and $Y$ be random variables, on probability spaces $(\Omega,\mu)$ and
--   $(\Omega',\nu)$ respectively. $X$ is said to be **smaller than $Y$ in the increasing convex
--   order**, written $X \le_{icx} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every increasing convex }
--     \varphi:\mathbb{R}\to\mathbb{R} \text{ for which the two expectations exist.}$$
--
--   This is the same univariate increasing convex order Chunk 04
--   (`StochasticOrders.MonotoneConvex`) defines, restated here because drafts cannot import
--   another mission's definitions. This chapter's own pitfall 1 notes that `M ≤icx N` for the
--   nonnegative-integer-valued `M`, `N` of Theorem 8.A.13 is a special case of this same
--   real-valued order (applied after the coercion `ℕ → ℝ`), not a separate discrete order.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, Chapter 4, Eq. (4.A.1) (restated locally)

import Mathlib

namespace StochasticOrders.StochasticConvexity

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The (univariate) increasing convex order `X ≤icx Y` (Shaked & Shanthikumar, *Stochastic
Orders*, Springer 2007, restated locally from Chapter 4's Eq. (4.A.1), the same shape this
series' Chunk 04 uses): a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y`
on a (possibly different) probability space `(Ω', ν)` in the increasing convex order if
`E[φ(X)] ≤ E[φ(Y)]` for every increasing convex function `φ : ℝ → ℝ` for which the two
expectations exist. Restated here, rather than imported, since drafts cannot import another
mission's definitions. -/
def IcxOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

end StochasticOrders.StochasticConvexity


