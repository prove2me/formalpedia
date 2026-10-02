-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SortedValues
-- name    : DiscreteConvex_LConvexFunctionsD_SortedValues
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:26.160348+00:00
-- url     : https://prove2.me/theorems/dd6c6a9d-3d1a-4ed9-97ed-154258c87b7d
-- title:
--   SortedValues
-- statement:
--   The distinct values of $p:V\to\mathbb R$, sorted in decreasing order.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The distinct values of `p : V → R`, sorted in decreasing order. -/
noncomputable def SortedValues (p : V → ℝ) : List ℝ :=
  (Finset.image p Finset.univ).sort (· ≥ ·)

end DiscreteConvex.LConvexFunctionsD


