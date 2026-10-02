-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_DualFeas
-- name    : DiscreteConvex_IntegralConvexityB_DualFeas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:33.990297+00:00
-- url     : https://prove2.me/theorems/8da63e4d-3b55-47c6-84ec-e45efc91a6fc
-- title:
--   Dual LP feasible region
-- statement:
--   $D=\{y:A^\top y\le c\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Eq. (3.45).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Eq. (3.45)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Eq. (3.45): the dual LP feasible region,
in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `D = \{y ∈ Rᵐ | Aᵀy ≤ c\}` (Eq. (3.45)), stated as `y⊤A ≤ c⊤` via `Matrix.vecMul`. -/
def DualFeas {V W : Type*} [Fintype W] (A : Matrix W V ℝ) (c : V → ℝ) : Set (W → ℝ) :=
  {y | ∀ j, Matrix.vecMul y A j ≤ c j}

end DiscreteConvex.IntegralConvexityB


