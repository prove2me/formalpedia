-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppNeg
-- name    : DiscreteConvex_EconomicEquilibriumB_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:52.750547+00:00
-- url     : https://prove2.me/theorems/ce0d5cb2-810e-4e4b-8c13-3bfd7b89e0b9
-- title:
--   SuppNeg
-- statement:
--   The negative support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The negative support for integer vectors. -/
def SuppNeg (x y : K → ℤ) : Finset K := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.EconomicEquilibriumB


