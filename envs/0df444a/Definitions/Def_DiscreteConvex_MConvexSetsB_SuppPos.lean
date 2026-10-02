-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_SuppPos
-- name    : DiscreteConvex_MConvexSetsB_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:05.44808+00:00
-- url     : https://prove2.me/theorems/b88dbd8b-9344-49a6-90d0-54f8d2d8437b
-- title:
--   SuppPos
-- statement:
--   The **positive support** $\operatorname{supp}^+(x-y) = \{v : x(v) > y(v)\}$ of the difference of two integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101 (citing Eq. (1.19)): the positive
support of a difference of integer vectors, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The positive support `supp⁺(x - y) = \{v : x(v) > y(v)\}`. -/
def SuppPos {V : Type*} (x y : V → ℤ) : Set V :=
  {v | y v < x v}

end DiscreteConvex.MConvexSetsB


