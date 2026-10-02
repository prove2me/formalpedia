-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeightR
-- name    : DiscreteConvex_MConvexFunctionsE_LinearWeightR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:52.002985+00:00
-- url     : https://prove2.me/theorems/64acc072-e265-4e5f-8ddd-5449ad8f9a1a
-- title:
--   LinearWeightR
-- statement:
--   $f[p](x) = f(x)-\langle p,x\rangle$ for real-domain $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69), real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69), real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f[p](x) = f(x) - ⟨p,x⟩` for real-domain `f`. -/
def LinearWeightR (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : (V → ℝ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * x v) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsE


