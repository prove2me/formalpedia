-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNeg
-- name    : DiscreteConvex_AlgorithmsB_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:38.547378+00:00
-- url     : https://prove2.me/theorems/ba0fab69-e79e-4ee1-ab3a-700e83bede59
-- title:
--   SuppNeg
-- statement:
--   The negative support, integer-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.AlgorithmsB


