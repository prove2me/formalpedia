-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeight
-- name    : DiscreteConvex_MConvexFunctionsE_LinearWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:48.307774+00:00
-- url     : https://prove2.me/theorems/64f2abcd-1fe7-4c53-afe1-9055c825309c
-- title:
--   LinearWeight
-- statement:
--   The linear-weighted function $f[p](x) = f(x) - \langle p,x\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The linear-weighted function `f[p](x) = f(x) - ⟨p,x⟩`. -/
def LinearWeight (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsE


