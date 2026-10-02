-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR
-- name    : DiscreteConvex_MConvexFunctionsD_LinearWeightR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:56.124433+00:00
-- url     : https://prove2.me/theorems/88cc4fc0-1f2e-4990-ace5-b03c4caf7031
-- title:
--   LinearWeightR
-- statement:
--   $f[p](x) = f(x)-\langle p,x\rangle$ for real-domain $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f[p](x) = f(x) - ⟨p,x⟩` for real-domain `f`. -/
def LinearWeightR (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : (V → ℝ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * x v) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsD


