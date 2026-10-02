-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_IntegralNeighborhood
-- name    : DiscreteConvex_IntegralConvexity_IntegralNeighborhood
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:24.313316+00:00
-- url     : https://prove2.me/theorems/8ac8b15f-fba0-4518-896a-7bbd44aa4253
-- title:
--   Integral neighborhood N(x) (Eq. 3.58)
-- statement:
--   The **integral neighborhood** of $x \in \mathbb R^n$ is $$N(x) = \{y \in \mathbb Z^n : \lfloor x_i \rfloor \le y_i \le \lceil x_i \rceil,\ 1 \le i \le n\},$$ Eq. (3.58); equivalently $\{y \in \mathbb Z^n : \|x-y\|_\infty < 1\}$ (Eq. (3.59)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.58)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.58): the integral neighborhood
`N(x)` of a real point, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The integral neighborhood `N(x) = {y ∈ Zⁿ : ⌊x_i⌋ ≤ y_i ≤ ⌈x_i⌉ for all i}` of a point
`x ∈ Rⁿ` (Eq. (3.58); equivalently `{y ∈ Zⁿ : ‖x - y‖_∞ < 1}`, Eq. (3.59)). -/
def IntegralNeighborhood {n : ℕ} (x : Fin n → ℝ) : Set (Fin n → ℤ) :=
  {y | ∀ i, ⌊x i⌋ ≤ y i ∧ y i ≤ ⌈x i⌉}

end DiscreteConvex.IntegralConvexity


