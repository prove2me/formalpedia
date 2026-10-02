-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppPosR
-- name    : DiscreteConvex_MConvexFunctionsD_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:32.900641+00:00
-- url     : https://prove2.me/theorems/01553ffc-faa6-4e9e-b286-f467baada2a6
-- title:
--   SuppPosR
-- statement:
--   The positive support for real vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppPosR (x y : V → ℝ) : Set V := {v | y v < x v}

end DiscreteConvex.MConvexFunctionsD


