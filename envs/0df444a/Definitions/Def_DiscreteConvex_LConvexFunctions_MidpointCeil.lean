-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_MidpointCeil
-- name    : DiscreteConvex_LConvexFunctions_MidpointCeil
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:45.813986+00:00
-- url     : https://prove2.me/theorems/35f7f32d-4be2-4ccb-99a7-4cd238697e64
-- title:
--   Componentwise ceiling of a midpoint
-- statement:
--   The componentwise ceiling $\lceil (p+q)/2 \rceil$ of the midpoint of $p,q \in \mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Eq. (7.7).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Eq. (7.7)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.180, Eq. (7.7): the componentwise ceiling of
the midpoint of two integer vectors, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The componentwise ceiling `⌈(p+q)/2⌉` of the midpoint of `p, q : Zⱽ`. -/
noncomputable def MidpointCeil {V : Type*} (p q : V → ℤ) : V → ℤ :=
  fun v => ⌈((p v + q v : ℤ) : ℝ) / 2⌉

end DiscreteConvex.LConvexFunctions


