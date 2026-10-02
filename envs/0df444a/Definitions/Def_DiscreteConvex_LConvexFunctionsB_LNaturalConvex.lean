-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
-- name    : DiscreteConvex_LConvexFunctionsB_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:05.147991+00:00
-- url     : https://prove2.me/theorems/def8e762-ca31-4076-bd74-229f770297d5
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift $\tilde g$ is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LiftedFunctionL

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift `g̃` is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.LConvexFunctionsB


