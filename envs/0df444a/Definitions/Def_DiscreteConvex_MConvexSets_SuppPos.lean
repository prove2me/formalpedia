-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_SuppPos
-- name    : DiscreteConvex_MConvexSets_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:17.159554+00:00
-- url     : https://prove2.me/theorems/09807fe7-7dc2-415c-baa2-b50d615f60f8
-- title:
--   Positive support of a vector difference
-- statement:
--   The **positive support** $\operatorname{supp}^+(x-y) = \{v : x(v) > y(v)\}$ of the difference of two integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101 (citing Eq. (1.19)): the positive
support of a difference of integer vectors, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- The positive support `supp⁺(x - y) = \{v : x(v) > y(v)\}`. -/
def SuppPos {V : Type*} (x y : V → ℤ) : Set V :=
  {v | y v < x v}

end DiscreteConvex.MConvexSets


