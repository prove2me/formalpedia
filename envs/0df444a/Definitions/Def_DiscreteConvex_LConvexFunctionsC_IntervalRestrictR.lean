-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntervalRestrictR
-- name    : DiscreteConvex_LConvexFunctionsC_IntervalRestrictR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:20.592994+00:00
-- url     : https://prove2.me/theorems/49726de4-694e-4ceb-85a1-52c7a62a68b8
-- title:
--   IntervalRestrictR
-- statement:
--   The restriction of $g$ to the real interval $[a,b]$ with $a,b\in(\mathbb R\cup\{\pm\infty\})^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.55), real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.55), real-variable analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The restriction of `g` to the real interval `[a,b]` with `a,b ∈ (R∪{±∞})ⱽ`. -/
noncomputable def IntervalRestrictR (g : (V → ℝ) → WithTop ℝ) (a b : V → WithBot (WithTop ℝ)) :
    (V → ℝ) → WithTop ℝ :=
  fun x => if (∀ v, a v ≤ ((x v : WithTop ℝ) : WithBot (WithTop ℝ)) ∧
      ((x v : WithTop ℝ) : WithBot (WithTop ℝ)) ≤ b v) then g x else ⊤

end DiscreteConvex.LConvexFunctionsC


