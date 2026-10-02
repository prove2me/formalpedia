-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppNeg
-- name    : DiscreteConvex_ConjugacyDualityB_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:26:47.140863+00:00
-- url     : https://prove2.me/theorems/f10cab7c-8162-4d65-9c8d-416ed9b558d8
-- title:
--   SuppNeg
-- statement:
--   The negative support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, real-variable analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support for integer vectors. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.ConjugacyDualityB


