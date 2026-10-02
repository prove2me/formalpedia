-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntegralNeighborhoodFinset
-- name    : DiscreteConvex_LConvexFunctionsC_IntegralNeighborhoodFinset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:31:54.384011+00:00
-- url     : https://prove2.me/theorems/e066ceff-2cc8-4a41-927e-7bfce02fe39f
-- title:
--   IntegralNeighborhoodFinset
-- statement:
--   The integral neighborhood $N(x)$ of $x\in\mathbb R^V$, Eq. (3.58).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(x)` of `x ∈ Rⱽ`, Eq. (3.58). -/
noncomputable def IntegralNeighborhoodFinset (x : V → ℝ) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc ⌊x v⌋ ⌈x v⌉)

end DiscreteConvex.LConvexFunctionsC


