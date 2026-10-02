-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPosR
-- name    : DiscreteConvex_MConvexFunctionsE_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:41.882804+00:00
-- url     : https://prove2.me/theorems/e623b1ed-f8a9-4d1d-be9e-32aa616961ca
-- title:
--   SuppPosR
-- statement:
--   The positive support for real vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support for real vectors. -/
def SuppPosR (x y : V → ℝ) : Set V := {v | y v < x v}

end DiscreteConvex.MConvexFunctionsE


