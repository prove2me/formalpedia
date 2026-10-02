-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppNeg
-- name    : DiscreteConvex_MConvexFunctionsC_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:11.982767+00:00
-- url     : https://prove2.me/theorems/8641444e-1a5b-4af5-b76d-2a4ce702cb3e
-- title:
--   SuppNeg
-- statement:
--   The negative support $\operatorname{supp}^-(x-y)$ of a difference of integer vectors, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctionsC


