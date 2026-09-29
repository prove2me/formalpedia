-- Prove2me | Definitions.Def_StochasticOrders_Convex_ConvexOrder
-- name    : StochasticOrders_Convex_ConvexOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:29:09.332744+00:00
-- url     : https://prove2.me/theorems/250e696b-dd76-4d08-bfb9-cbaff0f50b6e
-- title:
--   The convex order
-- statement:
--   Let $X$ be a real-valued random variable on a probability space $(\Omega,\mu)$ and let $Y$ be
--   a real-valued random variable on a (possibly different) probability space $(\Omega',\nu)$. $X$
--   is said to be **smaller than $Y$ in the convex order**, written $X \le_{cx} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every convex } \varphi:\mathbb{R}\to\mathbb{R}
--     \text{ for which the two expectations exist.}$$
--
--   Roughly speaking, convex functions take on their relatively larger values on the "extreme"
--   regions $(-\infty,a)\cup(b,\infty)$, so $X \le_{cx} Y$ says $Y$ is more likely to take on
--   extreme values than $X$: $Y$ is "more variable" than $X$. Together with `tailProb`
--   ($\bar F(x)=P\{X>x\}$) and `cdf` ($F(x)=P\{X\le x\}$, both cast to real numbers since they lie
--   in $[0,1]$ under a probability measure), this bundle supplies the machinery the chapter's
--   tail-integral characterizations (Theorem 3.A.1) are stated with.
--
--   **Formalization Note** `ConvexOn ℝ Set.univ φ` is Mathlib's convexity predicate; the
--   integrability of `φ ∘ X` and `φ ∘ Y` is stated as part of the `∀`, matching the book's "for
--   which the expectations exist" qualifier exactly rather than assuming it globally.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 109, Eq. (3.A.1)

import Mathlib

namespace StochasticOrders.Convex

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The convex order `X ≤cx Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 109,
Eq. (3.A.1)): a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y` on a
(possibly different) probability space `(Ω', ν)` in the convex order if `E[φ(X)] ≤ E[φ(Y)]` for
every convex function `φ : ℝ → ℝ` for which the two expectations exist. -/
def ConvexOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

/-- The survival function `P{X > x}` of a random variable `X` on `(Ω, μ)`, as a real number
(Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 110, notation `F̄`); well-defined
in `[0,1]` for a probability measure, so the `ENNReal.toReal` cast loses no information. -/
noncomputable def tailProb (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  (μ {ω | x < X ω}).toReal

/-- The distribution function `P{X ≤ x}` of a random variable `X` on `(Ω, μ)`, as a real number
(Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 110, notation `F`). -/
noncomputable def cdf (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  (μ {ω | X ω ≤ x}).toReal

end StochasticOrders.Convex


