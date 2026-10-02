-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppPos
-- name    : DiscreteConvex_MConvexFunctionsD_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:47:45.837553+00:00
-- url     : https://prove2.me/theorems/5b0755fe-1392-4896-ad60-a803cdc31f88
-- title:
--   SuppPos
-- statement:
--   The positive support $\operatorname{supp}^+(x-y)$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.MConvexFunctionsD


