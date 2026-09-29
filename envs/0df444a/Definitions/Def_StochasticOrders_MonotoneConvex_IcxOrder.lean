-- Prove2me | Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
-- name    : StochasticOrders_MonotoneConvex_IcxOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:57.567983+00:00
-- url     : https://prove2.me/theorems/240181b5-b9c0-4702-9be3-840ff1bc705a
-- title:
--   The increasing convex order
-- statement:
--   Let $X$ be a random variable on a probability space $(\Omega,\mu)$ and let $Y$ be a random
--   variable on a (possibly different) probability space $(\Omega',\nu)$. $X$ is said to be
--   **smaller than $Y$ in the increasing convex order**, written $X \le_{icx} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every increasing convex }
--     \varphi:\mathbb{R}\to\mathbb{R} \text{ for which the two expectations exist.}$$
--
--   Roughly speaking, if $X \le_{icx} Y$ then $X$ is both "smaller" and "less variable" than $Y$
--   in some stochastic sense. Together with `tailUpperIntegral` ($\int_x^\infty \bar F(u)\,du$,
--   the alternative form Theorem 4.A.2 uses), this bundle supplies the machinery the chapter's
--   tail-integral and submartingale-coupling characterizations are stated with.
--
--   **Formalization Note** `Monotone φ` is Mathlib's non-strict monotonicity, `ConvexOn ℝ
--   Set.univ φ` its convexity predicate on all of $\mathbb{R}$; the integrability of $\varphi\circ
--   X$ and $\varphi\circ Y$ is stated as part of the $\forall$, matching the book's "for which the
--   expectations exist" qualifier exactly rather than assuming it globally.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 181, Eq. (4.A.1)

import Mathlib

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The increasing convex order `X ≤icx Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 181, Eq. (4.A.1), increasing-convex case): a random variable `X` on `(Ω, μ)` is smaller
than a random variable `Y` on a (possibly different) probability space `(Ω', ν)` in the increasing
convex order if `E[φ(X)] ≤ E[φ(Y)]` for every increasing convex function `φ : ℝ → ℝ` for which the
two expectations exist. -/
def IcxOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

/-- The upper tail integral `∫_x^∞ F̄(u) du` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 182, Eq. (4.A.5)), the alternative,
integration-by-parts form of `E[(X-x)^+]` (Eq. (4.A.4)) that Theorem 4.A.2 characterizes `≤icx`
with. -/
noncomputable def tailUpperIntegral (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Ici x, (μ {ω | u < X ω}).toReal

end StochasticOrders.MonotoneConvex


