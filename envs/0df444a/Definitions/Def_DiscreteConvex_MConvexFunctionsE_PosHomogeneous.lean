-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_PosHomogeneous
-- name    : DiscreteConvex_MConvexFunctionsE_PosHomogeneous
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:26.080788+00:00
-- url     : https://prove2.me/theorems/50b921da-74bf-4a94-9d25-2cf0c6b01636
-- title:
--   PosHomogeneous
-- statement:
--   $g$ is positively homogeneous: $g(tx)=t\bullet g(x)$ for $t>0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (3.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (3.32)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_PosScalarMul

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is positively homogeneous: `g(tx)=t•g(x)` for `t>0`. -/
def PosHomogeneous (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ t : ℝ, 0 < t → g (fun v => t * x v) = PosScalarMul t (g x)

end DiscreteConvex.MConvexFunctionsE


