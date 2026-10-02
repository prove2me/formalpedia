-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppNegR
-- name    : DiscreteConvex_MConvexFunctionsC_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:39.688928+00:00
-- url     : https://prove2.me/theorems/a13a8199-7899-4616-b3a5-3f2f1118634c
-- title:
--   SuppNegR
-- statement:
--   The negative support $\operatorname{supp}^-(x-y)$ for real vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppNegR (x y : V → ℝ) : Set V := {v | x v < y v}

end DiscreteConvex.MConvexFunctionsC


