-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppPos
-- name    : DiscreteConvex_MConvexFunctionsC_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:12.586249+00:00
-- url     : https://prove2.me/theorems/be3f4c03-1140-4ec4-b815-c4b176352a6f
-- title:
--   SuppPos
-- statement:
--   The positive support $\operatorname{supp}^+(x-y)$ of a difference of integer vectors, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.MConvexFunctionsC


