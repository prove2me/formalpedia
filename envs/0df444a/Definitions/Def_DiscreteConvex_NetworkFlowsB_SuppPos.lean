-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_SuppPos
-- name    : DiscreteConvex_NetworkFlowsB_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:51.151165+00:00
-- url     : https://prove2.me/theorems/32d19961-6a3c-4a07-8514-b09b9901f57a
-- title:
--   SuppPos
-- statement:
--   The positive support, integer-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The positive support, integer-vector version. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.NetworkFlowsB


