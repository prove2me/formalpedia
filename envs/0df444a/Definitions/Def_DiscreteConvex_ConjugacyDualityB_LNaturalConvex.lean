-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
-- name    : DiscreteConvex_ConjugacyDualityB_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:30:52.799696+00:00
-- url     : https://prove2.me/theorems/591ba1ca-f09a-4b9e-a65d-a753a9fb0d01
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunctionL

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.ConjugacyDualityB


