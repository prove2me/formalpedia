-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma2
-- name    : DiscreteConvex_NetworkFlowsB_Gamma2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:45.947974+00:00
-- url     : https://prove2.me/theorems/10d60736-ef28-4cb4-a63e-b67a46464f2a
-- title:
--   Gamma2
-- statement:
--   The objective $\Gamma_2(\xi)=\sum_a\gamma(a)\xi(a)+f(\partial\xi)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.256, Eq. (9.42).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.256, Eq. (9.42)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ2(ξ) = Σ γ(a)ξ(a) + f(∂ξ)`. -/
def Gamma2 (tail head : A → V) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) :
    WithTop ℝ :=
  ((∑ a : A, gamma a * xi a : ℝ) : WithTop ℝ) + f (Boundary tail head xi)

end DiscreteConvex.NetworkFlowsB


