-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvex
-- name    : DiscreteConvex_MConvexFunctionsD_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:01.726097+00:00
-- url     : https://prove2.me/theorems/cea85a30-bd1e-4419-8fea-7cc9b134ecbb
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is M$^\natural$-convex: its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LiftedFunction

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.MConvexFunctionsD


