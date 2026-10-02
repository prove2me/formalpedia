-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_DeltaF
-- name    : DiscreteConvex_NetworkFlowsC_DeltaF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:37.119958+00:00
-- url     : https://prove2.me/theorems/2f2bd2e9-c903-4bc1-bf8c-b00b700cd316
-- title:
--   DeltaF
-- statement:
--   The directional difference $\Delta f(z;v,u)=f(z+\chi_v-\chi_u)-f(z)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The directional difference `Δf(z; v, u) = f(z + χ_v − χ_u) − f(z)`. -/
def DeltaF (f : (V → ℤ) → WithTop ℝ) (z : V → ℤ) (v u : V) : WithTop ℝ :=
  f (fun w => z w + (if w = v then (1:ℤ) else 0) - (if w = u then (1:ℤ) else 0)) - f z

end DiscreteConvex.NetworkFlowsC


