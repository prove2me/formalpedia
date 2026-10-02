-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
-- name    : DiscreteConvex_MConvexFunctionsC_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:29:20.618212+00:00
-- url     : https://prove2.me/theorems/814b893a-6a8d-41f6-82fa-b571ae460e5e
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is **M$^\natural$-convex**: its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LiftedFunction

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.MConvexFunctionsC


