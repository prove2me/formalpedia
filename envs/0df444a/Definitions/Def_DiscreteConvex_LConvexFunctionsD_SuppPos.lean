-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SuppPos
-- name    : DiscreteConvex_LConvexFunctionsD_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:38.554774+00:00
-- url     : https://prove2.me/theorems/e5fa19ad-3b1f-4321-90ba-711db6a58f75
-- title:
--   SuppPos
-- statement:
--   The positive support of $x-y$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, real-variable analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support of `x - y`. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.LConvexFunctionsD


