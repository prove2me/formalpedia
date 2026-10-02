-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
-- name    : DiscreteConvex_MConvexFunctionsC_LinearWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:22.733949+00:00
-- url     : https://prove2.me/theorems/a0090dbd-6cb3-47c8-8478-24de39140abd
-- title:
--   LinearWeight
-- statement:
--   The linear-weighted function $f[p](x) = f(x)-\langle p,x\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f[p](x) = f(x) - ⟨p,x⟩`. -/
def LinearWeight (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsC


