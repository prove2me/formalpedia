-- Prove2me | Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder
-- name    : StochasticOrders_MultivariateVariability_ConvexOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:56.633492+00:00
-- url     : https://prove2.me/theorems/16a897b0-09ac-4bca-874e-3dd6efd1f7a1
-- title:
--   The multivariate convex order
-- statement:
--   Let $X$ be a random vector, taking values in $\mathbb{R}^n$, on a probability space
--   $(\Omega,\mu)$, and let $Y$ be a random vector, taking values in $\mathbb{R}^n$, on a
--   (possibly different) probability space $(\Omega',\nu)$. $X$ is said to be **smaller than $Y$
--   in the multivariate convex order**, written $X \le_{cx} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every convex }
--     \varphi:\mathbb{R}^n\to\mathbb{R} \text{ for which the two expectations exist.}$$
--
--   This is the direct $n$-dimensional generalization of the univariate convex order (Chapter
--   III), with ordinary convexity on $\mathbb{R}^n$ (not a coordinatewise notion). Since each
--   coordinate projection $\varphi_i(x)=x_i$ and its negation $\psi_i(x)=-x_i$ are both convex,
--   $X\le_{cx}Y$ forces $E[X]=E[Y]$ (componentwise), Eq. (7.A.5).
--
--   **Formalization Note** `ConvexOn ℝ Set.univ φ` is Mathlib's ordinary convexity predicate on
--   all of $\mathbb{R}^n$ (drafted as `Fin n → ℝ`) — distinct from the *coordinatewise* order used
--   by `MultivariateOrder` (Chunk 06) or by "increasing" in `IcxOrder` below, and distinct from
--   the lattice-based *supermodularity* condition of Chunk 09. The integrability of $\varphi\circ
--   X$ and $\varphi\circ Y$ is stated as part of the $\forall$, matching "for which the
--   expectations exist."
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 324, Eq. (7.A.4)

import Mathlib

namespace StochasticOrders.MultivariateVariability

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The multivariate convex order `X ≤cx Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 324, Eq. (7.A.4)): an `n`-dimensional random vector `X` on `(Ω, μ)` is smaller than an
`n`-dimensional random vector `Y` on a (possibly different) probability space `(Ω', ν)` in the
multivariate convex order if `E[φ(X)] ≤ E[φ(Y)]` for every convex function `φ : (Fin n → ℝ) → ℝ`
(ordinary convexity on `ℝⁿ`, not a coordinatewise notion) for which the two expectations exist. -/
def ConvexOrder {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

end StochasticOrders.MultivariateVariability


