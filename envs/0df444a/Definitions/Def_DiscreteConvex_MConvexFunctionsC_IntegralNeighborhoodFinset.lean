-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
-- name    : DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:27.102251+00:00
-- url     : https://prove2.me/theorems/438ae616-42a2-4b46-b724-a177026d8800
-- title:
--   IntegralNeighborhoodFinset
-- statement:
--   The integral neighborhood $N(x)$ of $x \in \mathbb R^V$, as a finite set: integer vectors between $\lfloor x\rfloor$ and $\lceil x\rceil$ coordinatewise.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(x)` of `x ∈ Rⱽ`, as a `Finset`. -/
noncomputable def IntegralNeighborhoodFinset (x : V → ℝ) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc ⌊x v⌋ ⌈x v⌉)

end DiscreteConvex.MConvexFunctionsC


