-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvexR
-- name    : DiscreteConvex_ConjugacyDualityB_MNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:02.994641+00:00
-- url     : https://prove2.me/theorems/4cc02be5-3a3b-4fc7-af64-41b37d23d404
-- title:
--   MNaturalConvexR
-- statement:
--   $f$ is polyhedral M$^\natural$-convex: its lift is polyhedral M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunctionR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is polyhedral M♮-convex: its lift is polyhedral M-convex. -/
def MNaturalConvexR (f : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR (LiftedFunctionR f)

end DiscreteConvex.ConjugacyDualityB


