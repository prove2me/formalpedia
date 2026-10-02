-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppPos
-- name    : DiscreteConvex_EconomicEquilibriumB_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:51.079853+00:00
-- url     : https://prove2.me/theorems/19347152-bf27-425a-b6b2-758a999a434f
-- title:
--   SuppPos
-- statement:
--   The positive support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The positive support for integer vectors. -/
def SuppPos (x y : K → ℤ) : Finset K := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.EconomicEquilibriumB


