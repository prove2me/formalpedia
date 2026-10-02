-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNegR
-- name    : DiscreteConvex_MConvexFunctionsE_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:46.318848+00:00
-- url     : https://prove2.me/theorems/dcdc4f44-c71c-4bb5-8dd5-af8544db889d
-- title:
--   SuppNegR
-- statement:
--   The negative support for real vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support for real vectors. -/
def SuppNegR (x y : V → ℝ) : Set V := {v | x v < y v}

end DiscreteConvex.MConvexFunctionsE


