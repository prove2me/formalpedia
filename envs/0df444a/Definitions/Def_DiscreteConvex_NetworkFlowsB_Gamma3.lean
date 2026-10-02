-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma3
-- name    : DiscreteConvex_NetworkFlowsB_Gamma3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:38.99199+00:00
-- url     : https://prove2.me/theorems/6167eee9-cbe6-49e3-8d09-8370fc62e6b0
-- title:
--   Gamma3
-- statement:
--   The objective $\Gamma_3(\xi)=\sum_a f_a(\xi(a))+f(\partial\xi)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246, Eq. (9.7).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246, Eq. (9.7)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ3(ξ) = Σ fa(ξ(a)) + f(∂ξ)`. -/
def Gamma3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) :
    WithTop ℝ :=
  (∑ a : A, fa a (xi a)) + f (Boundary tail head xi)

end DiscreteConvex.NetworkFlowsB


