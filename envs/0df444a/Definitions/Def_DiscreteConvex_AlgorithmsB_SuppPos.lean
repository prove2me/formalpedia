-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPos
-- name    : DiscreteConvex_AlgorithmsB_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:34.676063+00:00
-- url     : https://prove2.me/theorems/5a6b7acc-5d18-45ce-9d7c-2abd5c8e0298
-- title:
--   SuppPos
-- statement:
--   The positive support, integer-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.AlgorithmsB


