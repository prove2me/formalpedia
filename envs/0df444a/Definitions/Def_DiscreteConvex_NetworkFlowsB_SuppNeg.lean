-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_SuppNeg
-- name    : DiscreteConvex_NetworkFlowsB_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:58.356564+00:00
-- url     : https://prove2.me/theorems/5e96356f-1d06-4182-ba6e-45dba8ae3acd
-- title:
--   SuppNeg
-- statement:
--   The negative support, integer-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The negative support, integer-vector version. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.NetworkFlowsB


