-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntegralNeighborhood
-- name    : DiscreteConvex_ConjugacyDualityC_IntegralNeighborhood
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:31.693266+00:00
-- url     : https://prove2.me/theorems/26b17a3c-7caf-42f4-b438-e63fb8b5ca59
-- title:
--   IntegralNeighborhood
-- statement:
--   The integral neighborhood $N(p)$ of $p\in\mathbb R^V$, as a set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58), set version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58), set version

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(p)` of `p ∈ Rⱽ`, as a set. -/
def IntegralNeighborhood (p : V → ℝ) : Set (V → ℤ) :=
  {y : V → ℤ | ∀ v, ⌊p v⌋ ≤ y v ∧ y v ≤ ⌈p v⌉}

end DiscreteConvex.ConjugacyDualityC


