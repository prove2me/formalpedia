-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ScaledConjugate
-- name    : DiscreteConvex_AlgorithmsC_ScaledConjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:43.985455+00:00
-- url     : https://prove2.me/theorems/9f6f885d-919c-4037-beeb-ba00fdb928f4
-- title:
--   ScaledConjugate
-- statement:
--   $g_\alpha(p)=g(\alpha p)/\alpha$, the conjugate-scaled dual function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, preceding Eq. (10.77).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, preceding Eq. (10.77)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_PosScalarMul

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g_α(p) = g(αp)/α`, the conjugate-scaled dual function. -/
noncomputable def ScaledConjugate (g : (V → ℤ) → WithTop ℝ) (alpha : ℤ) (p : V → ℤ) : WithTop ℝ :=
  PosScalarMul (1/(alpha : ℝ)) (g (fun v => alpha * p v))

end DiscreteConvex.AlgorithmsC


