-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma3Z
-- name    : DiscreteConvex_NetworkFlowsB_Gamma3Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:24:08.640605+00:00
-- url     : https://prove2.me/theorems/e173e6fd-4e6b-4a9e-9e43-57c0b6bb4f72
-- title:
--   Gamma3Z
-- statement:
--   The objective $\Gamma_3(\xi)=\sum_a f_a(\xi(a))+f(\partial\xi)$, integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.257-258, integer-flow version of Eq. (9.46).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.257-258, integer-flow version of Eq. (9.46)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ3(ξ) = Σ fa(ξ(a)) + f(∂ξ)`, integer flows. -/
def Gamma3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) :
    WithTop ℝ :=
  (∑ a : A, fa a (xi a)) + f (BoundaryZ tail head xi)

end DiscreteConvex.NetworkFlowsB


