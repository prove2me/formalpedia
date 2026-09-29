-- Prove2me | Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone
-- name    : StochasticOrders_LaplaceTransform_CompletelyMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:45.280981+00:00
-- url     : https://prove2.me/theorems/427bd31c-1b13-4330-9046-1dba9649c1e2
-- title:
--   Completely monotone functions
-- statement:
--   A function $\varphi : [0,\infty) \to \mathbb{R}$ is **completely monotone** if all its
--   derivatives $\varphi^{(n)}$ exist and
--
--   $$(-1)^n \varphi^{(n)}(x) \ge 0 \quad \text{for all } x > 0 \text{ and } n = 0, 1, 2, \dots.$$
--
--   Equivalently (a classical fact the book states but does not reprove), $\varphi$ is completely
--   monotone if and only if there is a measure $\mu$ on $(0,\infty)$ such that $\varphi(x) =
--   \int_0^\infty e^{-xu}\,\mu(du)$. The function $\varphi(x) = e^{-sx}$ is completely monotone for
--   every $s > 0$, which is what connects this notion to the Laplace transform order.
--
--   **Formalization Note** `CompletelyMonotone φ` bundles `ContDiff ℝ ⊤ φ` (all derivatives of `φ`
--   exist, as honest derivatives on all of `ℝ`, not merely on `[0,∞)`) together with the sign
--   condition on `iteratedDeriv n φ x` for every `n` and every `x > 0`. The smoothness conjunct is
--   needed: without it, `iteratedDeriv n φ x` silently defaults to `0` wherever the true derivative
--   fails to exist, which would make the sign condition alone too weak (vacuously true at any such
--   point) rather than a faithful reading of "all its derivatives exist".
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 234

import Mathlib

namespace StochasticOrders.LaplaceTransform

/-- A function `φ : ℝ → ℝ` is completely monotone (Shaked & Shanthikumar, *Stochastic Orders*,
Springer 2007, p. 234) if all its derivatives exist and `(-1)^n φ^(n)(x) ≥ 0` for every `x > 0` and
every `n = 0, 1, 2, …`. Existence of every derivative is carried by `ContDiff ℝ (⊤ : ℕ∞) φ` (`φ` is
`C^∞`), guarding against the junk value `iteratedDeriv n φ x = 0` that a nonexistent derivative
would otherwise silently supply. -/
def CompletelyMonotone (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x

end StochasticOrders.LaplaceTransform


