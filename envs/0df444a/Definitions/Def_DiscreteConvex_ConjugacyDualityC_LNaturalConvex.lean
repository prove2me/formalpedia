-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNaturalConvex
-- name    : DiscreteConvex_ConjugacyDualityC_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:05.5548+00:00
-- url     : https://prove2.me/theorems/9242aa48-fc45-467c-b113-2d2e45c17f6f
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedFunctionL

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.ConjugacyDualityC


