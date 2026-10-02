-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight
-- name    : DiscreteConvex_LConvexFunctionsB_LinearWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:21:03.232099+00:00
-- url     : https://prove2.me/theorems/b538fcd6-6262-4c91-85c9-d5e673c2063f
-- title:
--   LinearWeight
-- statement:
--   The linear-weighted function $g[p](x) = g(x) - \langle p,x\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The linear-weighted function `g[p](x) = g(x) - ⟨p,x⟩`. -/
def LinearWeight (g : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => g x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsB


