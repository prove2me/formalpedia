-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppNeg
-- name    : DiscreteConvex_MConvexFunctionsD_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:47:47.197269+00:00
-- url     : https://prove2.me/theorems/ebc0e525-c7ff-4063-9045-2f5966acd7ed
-- title:
--   SuppNeg
-- statement:
--   The negative support $\operatorname{supp}^-(x-y)$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctionsD


