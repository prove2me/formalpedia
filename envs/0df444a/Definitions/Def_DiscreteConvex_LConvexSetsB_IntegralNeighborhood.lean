-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_IntegralNeighborhood
-- name    : DiscreteConvex_LConvexSetsB_IntegralNeighborhood
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:42:03.262987+00:00
-- url     : https://prove2.me/theorems/9683ec93-6153-4fbc-b035-ece661d8a2c3
-- title:
--   IntegralNeighborhood
-- statement:
--   The **integral neighborhood** $N(p)$ of $p \in \mathbb R^V$ (Eq. (3.58)): integer vectors squeezed between $\lfloor p\rfloor$ and $\lceil p\rceil$ in every coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58), reused p.127-128.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58), reused p.127-128

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.99, Eq. (3.58): the integral
neighborhood of a real point, reused at p.127-128 for Theorem 5.10, in
`DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The **integral neighborhood** `N(p)` of `p ∈ Rⱽ` (Eq. (3.58)): integer vectors squeezed
between `⌊p⌋` and `⌈p⌉` in every coordinate. -/
def IntegralNeighborhood {V : Type*} (p : V → ℝ) : Set (V → ℤ) :=
  {y : V → ℤ | ∀ v, ⌊p v⌋ ≤ y v ∧ y v ≤ ⌈p v⌉}

end DiscreteConvex.LConvexSetsB


