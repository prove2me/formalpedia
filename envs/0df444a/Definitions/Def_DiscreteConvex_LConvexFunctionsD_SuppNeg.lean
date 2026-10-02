-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SuppNeg
-- name    : DiscreteConvex_LConvexFunctionsD_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:36.480218+00:00
-- url     : https://prove2.me/theorems/bcdbc6d6-a15f-4271-9d00-91a21bb60654
-- title:
--   SuppNeg
-- statement:
--   The negative support of $x-y$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, real-variable analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support of `x - y`. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.LConvexFunctionsD


