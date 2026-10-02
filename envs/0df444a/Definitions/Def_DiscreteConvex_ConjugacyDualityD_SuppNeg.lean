-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_SuppNeg
-- name    : DiscreteConvex_ConjugacyDualityD_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:39.539055+00:00
-- url     : https://prove2.me/theorems/c0d331b7-796e-414f-a292-3191fe291d5b
-- title:
--   SuppNeg
-- statement:
--   The negative support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support for integer vectors. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.ConjugacyDualityD


