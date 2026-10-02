-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_FracVec
-- name    : DiscreteConvex_LConvexSetsB_FracVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:42:03.647463+00:00
-- url     : https://prove2.me/theorems/4e0bc398-a0b7-43ff-b333-9d2d3db5492c
-- title:
--   FracVec
-- statement:
--   The **fractional part** of $p$, coordinatewise: $a(v) = p(v)-\lfloor p(v)\rfloor \in [0,1)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.127, preceding Eq. (5.11): the
fractional part of a real vector, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The **fractional part** of `p`, coordinatewise: `a(v) = p(v) - ⌊p(v)⌋ ∈ [0,1)`. -/
noncomputable def FracVec {V : Type*} (p : V → ℝ) : V → ℝ := fun v => p v - (⌊p v⌋ : ℝ)

end DiscreteConvex.LConvexSetsB


