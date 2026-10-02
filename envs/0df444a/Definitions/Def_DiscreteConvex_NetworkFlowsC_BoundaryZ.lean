-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ
-- name    : DiscreteConvex_NetworkFlowsC_BoundaryZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:12.93971+00:00
-- url     : https://prove2.me/theorems/b985ef65-92f3-4d1a-a81a-4c82f995d18a
-- title:
--   BoundaryZ
-- statement:
--   The boundary of an integer flow.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def BoundaryZ (tail head : A → V) (xi : A → ℤ) (v : V) : ℤ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), xi a)

end DiscreteConvex.NetworkFlowsC


