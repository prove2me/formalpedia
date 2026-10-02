-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormRestricted
-- name    : DiscreteConvex_MConvexFunctionsB_QuadraticFormRestricted
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:23.057302+00:00
-- url     : https://prove2.me/theorems/ceda979b-d69d-4da7-a5a5-6a8151505dea
-- title:
--   QuadraticFormRestricted
-- statement:
--   The quadratic form $f(x) = \tfrac12 x^\top A x$, restricted to $\{x : \sum_i x(i) = r\}$ ($+\infty$ elsewhere).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.139, Proposition 6.8(1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.139, Proposition 6.8(1)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.139, Proposition 6.8(1), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The quadratic form `f(x) = ½xᵀAx`, restricted to `\{x : Σx(i) = r\}` (`+∞` elsewhere). -/
noncomputable def QuadraticFormRestricted (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (r : ℤ) :
    (Fin n → ℤ) → WithTop ℝ :=
  fun x => if ∑ i, x i = r then
      (((1 / 2 : ℝ) * dotProduct (fun i => (x i : ℝ)) (A.mulVec (fun i => (x i : ℝ))) : ℝ) :
        WithTop ℝ)
    else ⊤

end DiscreteConvex.MConvexFunctionsB


