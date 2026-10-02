-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_QF
-- name    : DiscreteConvex_CombinatorialB_QF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:15.210648+00:00
-- url     : https://prove2.me/theorems/2ad54cf4-e28d-4484-8e1b-321cb2209d94
-- title:
--   Quadratic form (1/2)pᵀLp
-- statement:
--   The quadratic form $g(p) = \tfrac12 p^\top L p$ associated with a matrix $L$ (also used for $f(x)=\tfrac12x^\top Mx$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.64, Eq. (2.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.64, Eq. (2.14)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.64, Eq. (2.14): the quadratic form
`g(p) = (1/2)pᵀLp`, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- The quadratic form `QF L p = (1/2) pᵀ L p` associated with a (not necessarily symmetric)
matrix `L` (Eq. (2.14); also used for `f(x) = (1/2)xᵀMx` with `M` in place of `L`). -/
noncomputable def QF {V : Type*} [Fintype V] (L : Matrix V V ℝ) (p : V → ℝ) : ℝ :=
  (1 / 2) * dotProduct p (L.mulVec p)

end DiscreteConvex.CombinatorialB


