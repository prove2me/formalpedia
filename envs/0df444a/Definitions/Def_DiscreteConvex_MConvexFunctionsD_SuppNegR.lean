-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppNegR
-- name    : DiscreteConvex_MConvexFunctionsD_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:37.491135+00:00
-- url     : https://prove2.me/theorems/03ca5ea5-c22c-4363-85d0-7a6814fff70e
-- title:
--   SuppNegR
-- statement:
--   The negative support for real vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppNegR (x y : V → ℝ) : Set V := {v | x v < y v}

end DiscreteConvex.MConvexFunctionsD


