-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntegralNeighborhood
-- name    : DiscreteConvex_ConjugacyDualityB_IntegralNeighborhood
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:21.779974+00:00
-- url     : https://prove2.me/theorems/fa0a6f37-8e11-47fb-8421-20a9245badfd
-- title:
--   IntegralNeighborhood
-- statement:
--   The integral neighborhood $N(p)$ of $p\in\mathbb R^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58), set version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58), set version

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(p)` of `p ∈ Rⱽ`: integer vectors squeezed between `⌊p⌋` and
`⌈p⌉` in every coordinate. -/
def IntegralNeighborhood (p : V → ℝ) : Set (V → ℤ) :=
  {y : V → ℤ | ∀ v, ⌊p v⌋ ≤ y v ∧ y v ≤ ⌈p v⌉}

end DiscreteConvex.ConjugacyDualityB


