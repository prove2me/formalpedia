-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuasiSeparable
-- name    : DiscreteConvex_MConvexFunctionsB_QuasiSeparable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:24.933274+00:00
-- url     : https://prove2.me/theorems/40e10a5c-9d7c-4b54-8bac-691f38100c1e
-- title:
--   QuasiSeparable
-- statement:
--   A **quasi-separable convex function**, Eq. (6.32): $f(x) = f_0(\sum_i x(i)) + \sum_i f_i(x(i))$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, Eq. (6.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, Eq. (6.32)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, Eq. (6.32), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- A **quasi-separable convex function**, Eq. (6.32): `f(x) = f₀(Σx(i)) + Σfᵢ(x(i))`. -/
def QuasiSeparable {W : Type*} [Fintype W] (f0 : ℤ → WithTop ℝ) (fi : W → ℤ → WithTop ℝ) :
    (W → ℤ) → WithTop ℝ :=
  fun x => f0 (∑ v, x v) + ∑ v, fi v (x v)

end DiscreteConvex.MConvexFunctionsB


