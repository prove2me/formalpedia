-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormTotal
-- name    : DiscreteConvex_MConvexFunctionsB_QuadraticFormTotal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:25.847974+00:00
-- url     : https://prove2.me/theorems/4f46649d-7986-47d8-bc63-3cf32531bafe
-- title:
--   QuadraticFormTotal
-- statement:
--   The quadratic form $f(x) = \tfrac12 x^\top A x$, defined on all of $\mathbb Z^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.139, Proposition 6.8(2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.139, Proposition 6.8(2)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.139, Proposition 6.8(2), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The quadratic form `f(x) = ½xᵀAx`, defined on all of `Zⁿ`. -/
noncomputable def QuadraticFormTotal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℤ) → WithTop ℝ :=
  fun x => (((1 / 2 : ℝ) * dotProduct (fun i => (x i : ℝ)) (A.mulVec (fun i => (x i : ℝ))) : ℝ) :
    WithTop ℝ)

end DiscreteConvex.MConvexFunctionsB


