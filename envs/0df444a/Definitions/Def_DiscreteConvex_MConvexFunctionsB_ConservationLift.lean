-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_ConservationLift
-- name    : DiscreteConvex_MConvexFunctionsB_ConservationLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:14.706371+00:00
-- url     : https://prove2.me/theorems/399e2270-6f01-4f79-af75-6ac159e6caa6
-- title:
--   ConservationLift
-- statement:
--   The two-variable "conservation-law" lift of a univariate function $\psi$: $f(x) = \psi(x(1))$ if $x(1)+x(2)=0$, else $+\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, supporting Proposition 6.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, supporting Proposition 6.9

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, supporting Proposition 6.9, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The two-variable "conservation-law" lift of a univariate function: `f(x) = ψ(x(1))` if
`x(1)+x(2)=0`, else `+∞`. -/
def ConservationLift (psi : ℤ → WithTop ℝ) : (Fin 2 → ℤ) → WithTop ℝ :=
  fun x => if x 0 + x 1 = 0 then psi (x 0) else ⊤

end DiscreteConvex.MConvexFunctionsB


