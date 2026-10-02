-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IntegralPolyhedralFunctionR
-- name    : DiscreteConvex_LConvexFunctionsD_IntegralPolyhedralFunctionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:29.867207+00:00
-- url     : https://prove2.me/theorems/9a956c15-ee13-4766-9ed0-e1c1533115ce
-- title:
--   IntegralPolyhedralFunctionR
-- statement:
--   $g$ has arg-min-integrality: $\arg\min g[-p]$ is an integral polyhedron for every weight $p$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Eq. (6.75)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Eq. (6.75)-analogue

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` has arg-min-integrality: `arg min g[-p]` is an integral polyhedron for every weight
`p`. -/
def IntegralPolyhedralFunctionR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, (ArgMinR (LinearWeightR g p)).Nonempty → IsIntegralPolyhedron (ArgMinR (LinearWeightR g p))

end DiscreteConvex.LConvexFunctionsD


