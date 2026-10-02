-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex
-- name    : DiscreteConvex_ConjugacyDualityD_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:59:28.038157+00:00
-- url     : https://prove2.me/theorems/60ae4385-f10f-4f4f-ae48-8a459503d6aa
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is M$^\natural$-convex: its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LiftedFunction

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮-convex: its lift is M-convex. -/
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.ConjugacyDualityD


