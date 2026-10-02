-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegralNeighborhood
-- name    : DiscreteConvex_IntegralConvexityC_IntegralNeighborhood
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:04.781011+00:00
-- url     : https://prove2.me/theorems/530716da-7953-48cc-a09c-bc3333757085
-- title:
--   Integral neighborhood N(x)
-- statement:
--   $N(x)=\{y\in\mathbb Z^n:\lfloor x_i\rfloor\le y_i\le\lceil x_i\rceil\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.58)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.58): the integral neighborhood
`N(x)`, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `N(x) = \{y ∈ Zⁿ : ⌊x_i⌋ ≤ y_i ≤ ⌈x_i⌉\}` (Eq. (3.58)). -/
def IntegralNeighborhood {n : ℕ} (x : Fin n → ℝ) : Set (Fin n → ℤ) :=
  {y | ∀ i, ⌊x i⌋ ≤ y i ∧ y i ≤ ⌈x i⌉}

end DiscreteConvex.IntegralConvexityC


