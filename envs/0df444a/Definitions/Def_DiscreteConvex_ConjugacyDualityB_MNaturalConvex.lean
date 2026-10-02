-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex
-- name    : DiscreteConvex_ConjugacyDualityB_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:32:27.274746+00:00
-- url     : https://prove2.me/theorems/7a20b694-0f53-470d-8de0-31cdf328d9e4
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is M$^\natural$-convex: its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunction

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮-convex: its lift is M-convex. -/
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.ConjugacyDualityB


