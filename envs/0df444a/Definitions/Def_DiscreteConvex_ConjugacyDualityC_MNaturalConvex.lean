-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNaturalConvex
-- name    : DiscreteConvex_ConjugacyDualityC_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:18.710602+00:00
-- url     : https://prove2.me/theorems/a12da31f-a59d-41f9-99b7-46c2b38e7778
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is M$^\natural$-convex: its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedFunction

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮-convex: its lift is M-convex. -/
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.ConjugacyDualityC


