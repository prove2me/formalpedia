-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_SuppPos
-- name    : DiscreteConvex_ConjugacyDualityC_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:40:56.553866+00:00
-- url     : https://prove2.me/theorems/7402fbf9-ae6e-4bca-9379-4a274cd485ea
-- title:
--   SuppPos
-- statement:
--   The positive support for integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support for integer vectors. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.ConjugacyDualityC


