-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LinearWeightR
-- name    : DiscreteConvex_ConjugacyDualityB_LinearWeightR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:48.180029+00:00
-- url     : https://prove2.me/theorems/d1862938-79ec-4d20-92e4-c0b70b6926d8
-- title:
--   LinearWeightR
-- statement:
--   $g[p](x) = g(x) - \langle p,x\rangle$ for real-domain $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g[p](x) = g(x) - ⟨p,x⟩` for real-domain `g`. -/
def LinearWeightR (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : (V → ℝ) → WithTop ℝ :=
  fun x => g x + (((-(∑ v, p v * x v) : ℝ)) : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityB


