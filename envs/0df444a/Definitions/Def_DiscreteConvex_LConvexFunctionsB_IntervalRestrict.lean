-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_IntervalRestrict
-- name    : DiscreteConvex_LConvexFunctionsB_IntervalRestrict
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:21:11.41531+00:00
-- url     : https://prove2.me/theorems/35f3eaef-00fe-438e-838b-0ea7406f3299
-- title:
--   IntervalRestrict
-- statement:
--   The restriction of $g$ to the integer interval $[a,b]$ with $a,b\in(\mathbb Z\cup\{\pm\infty\})^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.55).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.55)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The restriction of `g` to the integer interval `[a,b]` with `a,b ∈ (Z∪{±∞})ⱽ`, Eq. (3.55). -/
noncomputable def IntervalRestrict (g : (V → ℤ) → WithTop ℝ) (a b : V → WithBot (WithTop ℤ)) :
    (V → ℤ) → WithTop ℝ :=
  fun x => if (∀ v, a v ≤ ((x v : WithTop ℤ) : WithBot (WithTop ℤ)) ∧
      ((x v : WithTop ℤ) : WithBot (WithTop ℤ)) ≤ b v) then g x else ⊤

end DiscreteConvex.LConvexFunctionsB


