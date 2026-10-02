-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_MidpointFloor
-- name    : DiscreteConvex_LConvexFunctions_MidpointFloor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:41.3831+00:00
-- url     : https://prove2.me/theorems/224081e0-0606-4544-b523-8c2cfd960d42
-- title:
--   Componentwise floor of a midpoint
-- statement:
--   The componentwise floor $\lfloor (p+q)/2 \rfloor$ of the midpoint of $p,q \in \mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Eq. (7.7).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Eq. (7.7)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.180, Eq. (7.7): the componentwise floor of the
midpoint of two integer vectors, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The componentwise floor `⌊(p+q)/2⌋` of the midpoint of `p, q : Zⱽ`. -/
noncomputable def MidpointFloor {V : Type*} (p q : V → ℤ) : V → ℤ :=
  fun v => ⌊((p v + q v : ℤ) : ℝ) / 2⌋

end DiscreteConvex.LConvexFunctions


