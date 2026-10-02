-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_SuppNeg
-- name    : DiscreteConvex_MConvexSets_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:17.940579+00:00
-- url     : https://prove2.me/theorems/d60544d4-fdb2-47fb-b3b7-0a38e18ace1e
-- title:
--   Negative support of a vector difference
-- statement:
--   The **negative support** $\operatorname{supp}^-(x-y) = \{v : x(v) < y(v)\}$ of the difference of two integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101 (citing Eq. (1.19)): the negative
support of a difference of integer vectors, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- The negative support `supp⁻(x - y) = \{v : x(v) < y(v)\}`. -/
def SuppNeg {V : Type*} (x y : V → ℤ) : Set V :=
  {v | x v < y v}

end DiscreteConvex.MConvexSets


