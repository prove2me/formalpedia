-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
-- name    : DiscreteConvex_ConjugacyDualityD_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:03.507008+00:00
-- url     : https://prove2.me/theorems/e494dbe4-5121-43bf-9a42-4cbdb8b283fa
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LiftedFunctionL

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.ConjugacyDualityD


