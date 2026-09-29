-- Prove2me | Definitions.Def_StochasticOrders_MultivariateVariability_IcxOrder
-- name    : StochasticOrders_MultivariateVariability_IcxOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:22.296031+00:00
-- url     : https://prove2.me/theorems/6dd8af6d-8974-4ddb-9df6-e24f12672b71
-- title:
--   The multivariate increasing convex order
-- statement:
--   Let $X$ and $Y$ be $n$-dimensional random vectors, on probability spaces $(\Omega,\mu)$ and
--   $(\Omega',\nu)$ respectively. $X$ is said to be **smaller than $Y$ in the increasing convex
--   order**, written $X \le_{icx} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every increasing convex }
--     \varphi:\mathbb{R}^n\to\mathbb{R} \text{ for which the two expectations exist,}$$
--
--   where "increasing" is with respect to the coordinatewise order on $\mathbb{R}^n$ and
--   "convex" is ordinary convexity on $\mathbb{R}^n$. This is the direct $n$-dimensional
--   generalization of Chapter IV's increasing convex order, defined in a similar fashion to its
--   univariate counterpart.
--
--   **Formalization Note** `Monotone φ` for `φ : (Fin n → ℝ) → ℝ` uses Mathlib's default
--   coordinatewise (`Pi`) order on `Fin n → ℝ`, matching the book's own coordinatewise
--   "increasing"; `ConvexOn ℝ Set.univ φ` is ordinary convexity, matching `ConvexOrder` above.
--   Deliberately a *separate* definition from `ConvexOrder`, since Theorem 7.A.12 (not drafted
--   here, see `STATUS.md`) relates the two nontrivially, and conflating them would trivialize
--   such a relationship.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 323, Eq. (7.A.1)

import Mathlib

namespace StochasticOrders.MultivariateVariability

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The multivariate increasing convex order `X ≤icx Y` (Shaked & Shanthikumar, *Stochastic
Orders*, Springer 2007, p. 323, Eq. (7.A.1), increasing-convex case): an `n`-dimensional random
vector `X` on `(Ω, μ)` is smaller than an `n`-dimensional random vector `Y` on a (possibly
different) probability space `(Ω', ν)` in the increasing convex order if `E[φ(X)] ≤ E[φ(Y)]` for
every function `φ : (Fin n → ℝ) → ℝ` that is both increasing (coordinatewise, Mathlib's `Pi`
order on `Fin n → ℝ`) and convex (ordinary convexity on `ℝⁿ`), for which the two expectations
exist. -/
def IcxOrder {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ →
    Integrable (φ ∘ Y) ν → ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

end StochasticOrders.MultivariateVariability


