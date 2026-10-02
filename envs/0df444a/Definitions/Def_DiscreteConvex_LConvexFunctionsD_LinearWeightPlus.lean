-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightPlus
-- name    : DiscreteConvex_LConvexFunctionsD_LinearWeightPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:56.390158+00:00
-- url     : https://prove2.me/theorems/f3ae2f27-824e-488e-b857-5792bacc655b
-- title:
--   LinearWeightPlus
-- statement:
--   $g[x](p) = g(p) + \langle p,x\rangle$, the L-side linear perturbation convention.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g[x](p) = g(p) + ⟨p,x⟩`, the L-side linear perturbation convention. -/
def LinearWeightPlus (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun p => g p + (((∑ v, x v * (p v : ℝ) : ℝ)) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


