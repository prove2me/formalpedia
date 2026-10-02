-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma2Z
-- name    : DiscreteConvex_NetworkFlowsB_Gamma2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:24:02.249188+00:00
-- url     : https://prove2.me/theorems/88c606f9-0167-4a8a-be02-a8dd9f9f5a74
-- title:
--   Gamma2Z
-- statement:
--   The objective $\Gamma_2(\xi)=\sum_a\gamma(a)\xi(a)+f(\partial\xi)$, integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, integer-flow version of Eq. (9.42).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, integer-flow version of Eq. (9.42)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ2(ξ) = Σ γ(a)ξ(a) + f(∂ξ)`, integer flows. -/
def Gamma2Z (tail head : A → V) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) :
    WithTop ℝ :=
  ((∑ a : A, gamma a * (xi a : ℝ) : ℝ) : WithTop ℝ) + f (BoundaryZ tail head xi)

end DiscreteConvex.NetworkFlowsB


