-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_LinearWeight
-- name    : DiscreteConvex_MConvexFunctionsB_LinearWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:24.985442+00:00
-- url     : https://prove2.me/theorems/44330dfe-694a-46c2-91f4-3b0c62789020
-- title:
--   LinearWeight
-- statement:
--   The linear-weighted function $f[p](x) = f(x) - \langle p,x\rangle$, Eq. (3.69).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69), reused pp.143,147-148.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69), reused pp.143,147-148

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Eq. (3.69), reused pp.143,147-148, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The linear-weighted function `f[p](x) = f(x) - ⟨p,x⟩`, Eq. (3.69). -/
def LinearWeight {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsB


