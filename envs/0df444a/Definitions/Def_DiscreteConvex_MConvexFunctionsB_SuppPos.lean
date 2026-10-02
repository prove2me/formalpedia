-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
-- name    : DiscreteConvex_MConvexFunctionsB_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:05:38.517732+00:00
-- url     : https://prove2.me/theorems/ddb89ddd-23e1-457c-8b02-ec91780b8ab7
-- title:
--   SuppPos
-- statement:
--   The positive support $\operatorname{supp}^+(x-y)$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The positive support `supp⁺(x - y)`, as a `Finset` (`V` is finite). -/
def SuppPos {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.MConvexFunctionsB


