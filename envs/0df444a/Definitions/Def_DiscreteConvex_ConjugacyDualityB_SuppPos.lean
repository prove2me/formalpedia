-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppPos
-- name    : DiscreteConvex_ConjugacyDualityB_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:26:46.816619+00:00
-- url     : https://prove2.me/theorems/5dd572fa-8e37-4423-92e4-1b721a54822f
-- title:
--   SuppPos
-- statement:
--   The positive support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, real-variable analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support for integer vectors. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.ConjugacyDualityB


