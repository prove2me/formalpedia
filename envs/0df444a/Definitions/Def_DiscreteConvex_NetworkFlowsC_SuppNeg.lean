-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNeg
-- name    : DiscreteConvex_NetworkFlowsC_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:36.898981+00:00
-- url     : https://prove2.me/theorems/bc3a3007-4104-4681-8ec5-5f70091b4af4
-- title:
--   SuppNeg
-- statement:
--   The negative support, integer-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.NetworkFlowsC


