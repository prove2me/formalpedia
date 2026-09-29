-- Prove2me | Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder
-- name    : StochasticOrders_Multivariate_MultivariateOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:21.489425+00:00
-- url     : https://prove2.me/theorems/573f8dd3-cab4-4e64-9823-15c94e491dc7
-- title:
--   The usual multivariate stochastic order
-- statement:
--   Let $X$ be a random vector, taking values in $\mathbb{R}^n$, on a probability space
--   $(\Omega,\mu)$, and let $Y$ be a random vector, taking values in $\mathbb{R}^n$, on a
--   (possibly different) probability space $(\Omega',\nu)$. $X$ is said to be **smaller than $Y$
--   in the usual multivariate stochastic order**, written $X \le_{st} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every increasing }
--     \varphi:\mathbb{R}^n\to\mathbb{R} \text{ for which the two expectations exist,}$$
--
--   where "increasing" means with respect to the coordinatewise partial order on $\mathbb{R}^n$
--   ($x \le y$ iff $x_i \le y_i$ for every $i$). This is the direct $n$-dimensional generalization
--   of the univariate usual stochastic order: (6.B.4) says $X\le_{st}Y$ iff $P\{X\in U\}\le
--   P\{Y\in U\}$ for every increasing (upper) set $U\subseteq\mathbb{R}^n$, and the book derives
--   the function-class form above from that as a limit of simple functions.
--
--   **Formalization Note** Random vectors are formalized as functions into `Fin n → ℝ`, which
--   Mathlib equips with the coordinatewise (`Pi`) order by default — exactly the order the book
--   uses — so `Monotone φ` for `φ : (Fin n → ℝ) → ℝ` already means "increasing" in the book's
--   sense with no extra predicate needed. The integrability of $\varphi\circ X$ and $\varphi\circ
--   Y$ is stated as part of the $\forall$, matching "for which the expectations exist."
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 266, Eq. (6.B.4)

import Mathlib

namespace StochasticOrders.Multivariate

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The usual multivariate stochastic order `X ≤st Y` (Shaked & Shanthikumar, *Stochastic
Orders*, Springer 2007, p. 266, Eq. (6.B.4)): an `n`-dimensional random vector `X` on `(Ω, μ)` is
smaller than an `n`-dimensional random vector `Y` on a (possibly different) probability space
`(Ω', ν)` in the usual multivariate stochastic order if `E[φ(X)] ≤ E[φ(Y)]` for every increasing
function `φ : (Fin n → ℝ) → ℝ` (increasing with respect to the coordinatewise order on
`Fin n → ℝ`, i.e. Mathlib's `Pi` order) for which the two expectations exist. -/
def MultivariateOrder {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, Monotone φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

end StochasticOrders.Multivariate


