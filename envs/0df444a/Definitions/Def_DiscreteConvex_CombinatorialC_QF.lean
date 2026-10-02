-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_QF
-- name    : DiscreteConvex_CombinatorialC_QF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:01.457314+00:00
-- url     : https://prove2.me/theorems/bf4954f9-7b07-4c0e-8aeb-fc8a8fd1359d
-- title:
--   Quadratic form (1/2)pᵀLp
-- statement:
--   $g(p)=\tfrac12p^\top Lp$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.64, Eq. (2.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.64, Eq. (2.14)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.64, Eq. (2.14): the quadratic form
`g(p) = (1/2)pᵀLp`, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The quadratic form `QF L p = (1/2) pᵀ L p`. -/
noncomputable def QF {V : Type*} [Fintype V] (L : Matrix V V ℝ) (p : V → ℝ) : ℝ :=
  (1 / 2) * dotProduct p (L.mulVec p)

end DiscreteConvex.CombinatorialC


