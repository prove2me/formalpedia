-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPos
-- name    : DiscreteConvex_NetworkFlowsC_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:35.86299+00:00
-- url     : https://prove2.me/theorems/6f81dbcc-dded-4aa4-87b0-3dcb8d247696
-- title:
--   SuppPos
-- statement:
--   The positive support, integer-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.NetworkFlowsC


