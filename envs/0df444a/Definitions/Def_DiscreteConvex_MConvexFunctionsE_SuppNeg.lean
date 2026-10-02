-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
-- name    : DiscreteConvex_MConvexFunctionsE_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:37.007253+00:00
-- url     : https://prove2.me/theorems/8e3310ba-6e49-46d3-bad8-d753d765b2ce
-- title:
--   SuppNeg
-- statement:
--   The negative support $\operatorname{supp}^-(x-y)$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support of `x - y`. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctionsE


