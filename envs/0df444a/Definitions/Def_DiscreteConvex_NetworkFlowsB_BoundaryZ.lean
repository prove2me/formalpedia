-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ
-- name    : DiscreteConvex_NetworkFlowsB_BoundaryZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:38.214027+00:00
-- url     : https://prove2.me/theorems/fb7af54f-f372-4075-9318-2d42681846ba
-- title:
--   BoundaryZ
-- statement:
--   The boundary of an integer flow.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1), integer version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1), integer version

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The boundary of an integer flow. -/
def BoundaryZ (tail head : A → V) (xi : A → ℤ) (v : V) : ℤ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), xi a)

end DiscreteConvex.NetworkFlowsB


