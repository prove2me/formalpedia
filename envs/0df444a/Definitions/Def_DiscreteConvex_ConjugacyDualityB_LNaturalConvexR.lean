-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvexR
-- name    : DiscreteConvex_ConjugacyDualityB_LNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:11.224362+00:00
-- url     : https://prove2.me/theorems/1a47ecda-d579-436d-8634-d015e766916a
-- title:
--   LNaturalConvexR
-- statement:
--   $g$ is polyhedral L$^\natural$-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunctionLR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is polyhedral L♮-convex. -/
def LNaturalConvexR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  SBFR (LiftedFunctionLR g) ∧ TRFR (LiftedFunctionLR g)

end DiscreteConvex.ConjugacyDualityB


