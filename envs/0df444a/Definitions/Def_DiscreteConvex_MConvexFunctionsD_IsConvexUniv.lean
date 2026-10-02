-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsConvexUniv
-- name    : DiscreteConvex_MConvexFunctionsD_IsConvexUniv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:41.842581+00:00
-- url     : https://prove2.me/theorems/25b82e68-951c-4a24-a945-dfdadcfd2428
-- title:
--   IsConvexUniv
-- statement:
--   $\phi:\mathbb R\to\mathbb R\cup\{+\infty\}$ is convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `φ : R → R ∪ {+∞}` is convex. -/
def IsConvexUniv (phi : ℝ → WithTop ℝ) : Prop :=
  ∀ x y : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    phi (t * x + (1 - t) * y) ≤ PosScalarMul t (phi x) + PosScalarMul (1 - t) (phi y)

end DiscreteConvex.MConvexFunctionsD


