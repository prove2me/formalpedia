-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppPosR
-- name    : DiscreteConvex_MConvexFunctionsC_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:38.066964+00:00
-- url     : https://prove2.me/theorems/5e693ef0-74ad-40fd-bbfd-3aad8374ad07
-- title:
--   SuppPosR
-- statement:
--   The positive support $\operatorname{supp}^+(x-y)$ for real vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppPosR (x y : V → ℝ) : Set V := {v | y v < x v}

end DiscreteConvex.MConvexFunctionsC


