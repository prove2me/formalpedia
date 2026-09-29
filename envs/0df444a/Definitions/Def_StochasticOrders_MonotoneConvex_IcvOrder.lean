-- Prove2me | Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder
-- name    : StochasticOrders_MonotoneConvex_IcvOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:23.386047+00:00
-- url     : https://prove2.me/theorems/47055fda-2d26-4ae0-868f-d354edde29ed
-- title:
--   The increasing concave order
-- statement:
--   Let $X$ be a random variable on a probability space $(\Omega,\mu)$ and let $Y$ be a random
--   variable on a (possibly different) probability space $(\Omega',\nu)$. $X$ is said to be
--   **smaller than $Y$ in the increasing concave order**, written $X \le_{icv} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every increasing concave }
--     \varphi:\mathbb{R}\to\mathbb{R} \text{ for which the two expectations exist.}$$
--
--   Roughly speaking, if $X \le_{icv} Y$ then $X$ is both "smaller" and "more variable" than $Y$
--   in some stochastic sense — the mirror image of $\le_{icx}$ under the function-class swap from
--   convex to concave. Together with `tailLowerIntegral` ($\int_{-\infty}^x F(u)\,du$, the
--   alternative form Theorem 4.A.2 uses), this bundle supplies the machinery this chapter's
--   tail-integral and supermartingale-coupling characterizations are stated with.
--
--   **Formalization Note** Deliberately a *separate* definition from `IcxOrder`, not a single
--   order parametrized by an `Or` of function classes or derived from `IcxOrder` by negation —
--   Theorem 4.A.1 (the duality relation) is exactly the nontrivial statement that the two are
--   related by negating the random variables, and stating that as a genuine `↔` between two
--   independently-defined predicates is what gives the theorem content (see
--   `icx_icv_duality`'s Formalization Note).
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 181, Eq. (4.A.1)

import Mathlib

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The increasing concave order `X ≤icv Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 181, Eq. (4.A.1), increasing-concave case): a random variable `X` on `(Ω, μ)` is smaller
than a random variable `Y` on a (possibly different) probability space `(Ω', ν)` in the increasing
concave order if `E[φ(X)] ≤ E[φ(Y)]` for every increasing concave function `φ : ℝ → ℝ` for which
the two expectations exist. -/
def IcvOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConcaveOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

/-- The lower tail integral `∫_{-∞}^x F(u) du` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 182, Eq. (4.A.7)), the alternative,
integration-by-parts form of `E[(X-x)^-]` (Eq. (4.A.6)) that Theorem 4.A.2 characterizes `≤icv`
with. -/
noncomputable def tailLowerIntegral (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Iic x, (μ {ω | X ω ≤ u}).toReal

end StochasticOrders.MonotoneConvex


