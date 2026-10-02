-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_Gamma2Z
-- name    : DiscreteConvex_NetworkFlowsC_Gamma2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:55.331365+00:00
-- url     : https://prove2.me/theorems/ddf9bda9-98ea-4480-9b66-dd06b55c047f
-- title:
--   Gamma2Z
-- statement:
--   The objective $\Gamma_2(\xi)=\sum_a\gamma(a)\xi(a)+f(\partial\xi)$, integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def Gamma2Z (tail head : A → V) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) :
    WithTop ℝ :=
  ((∑ a : A, gamma a * (xi a : ℝ) : ℝ) : WithTop ℝ) + f (BoundaryZ tail head xi)

end DiscreteConvex.NetworkFlowsC


