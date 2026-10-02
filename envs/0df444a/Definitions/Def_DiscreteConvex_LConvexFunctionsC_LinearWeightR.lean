-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR
-- name    : DiscreteConvex_LConvexFunctionsC_LinearWeightR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:16.839981+00:00
-- url     : https://prove2.me/theorems/77032cc7-8676-41a6-abfa-e9c151efba0d
-- title:
--   LinearWeightR
-- statement:
--   $g[p](x) = g(x) - \langle p,x\rangle$ for real-domain $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g[p](x) = g(x) - ⟨p,x⟩` for real-domain `g`. -/
def LinearWeightR (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : (V → ℝ) → WithTop ℝ :=
  fun x => g x + (((-(∑ v, p v * x v) : ℝ)) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsC


