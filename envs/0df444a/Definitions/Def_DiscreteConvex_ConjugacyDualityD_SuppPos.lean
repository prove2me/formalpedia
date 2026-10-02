-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_SuppPos
-- name    : DiscreteConvex_ConjugacyDualityD_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:42.444646+00:00
-- url     : https://prove2.me/theorems/00d1d6c8-914e-4af4-b057-0b0d79b6cf3b
-- title:
--   SuppPos
-- statement:
--   The positive support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support for integer vectors. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.ConjugacyDualityD


