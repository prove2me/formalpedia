-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
-- name    : DiscreteConvex_LConvexFunctionsD_LinearWeightR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:21.26605+00:00
-- url     : https://prove2.me/theorems/6a3dedf0-98fa-4d2a-bb40-66954dab18bb
-- title:
--   LinearWeightR
-- statement:
--   $g[p](x) = g(x) - \langle p,x\rangle$ for real-domain $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g[p](x) = g(x) - ⟨p,x⟩` for real-domain `g`. -/
def LinearWeightR (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : (V → ℝ) → WithTop ℝ :=
  fun x => g x + (((-(∑ v, p v * x v) : ℝ)) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


