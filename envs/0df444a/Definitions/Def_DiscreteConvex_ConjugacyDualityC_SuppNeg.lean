-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_SuppNeg
-- name    : DiscreteConvex_ConjugacyDualityC_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:00.699213+00:00
-- url     : https://prove2.me/theorems/d22f5b77-6795-4d13-9199-19147edb953d
-- title:
--   SuppNeg
-- statement:
--   The negative support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support for integer vectors. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.ConjugacyDualityC


