-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
-- name    : DiscreteConvex_MConvexFunctionsE_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:35.961977+00:00
-- url     : https://prove2.me/theorems/537c0c98-89bc-4f69-8706-b3a856576013
-- title:
--   SuppPos
-- statement:
--   The positive support $\operatorname{supp}^+(x-y)$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support of `x - y`. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.MConvexFunctionsE


