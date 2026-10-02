-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosHomogeneous
-- name    : DiscreteConvex_MConvexFunctionsD_PosHomogeneous
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:51:03.233627+00:00
-- url     : https://prove2.me/theorems/18f4e4eb-d914-416d-8f12-c946dbbdcb02
-- title:
--   PosHomogeneous
-- statement:
--   $g$ is positively homogeneous: $g(tx)=t\bullet g(x)$ for $t>0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (3.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (3.32)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is positively homogeneous, Eq. (3.32): `g(tx) = t • g(x)` for `t > 0`. -/
def PosHomogeneous (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ t : ℝ, 0 < t → g (fun v => t * x v) = PosScalarMul t (g x)

end DiscreteConvex.MConvexFunctionsD


