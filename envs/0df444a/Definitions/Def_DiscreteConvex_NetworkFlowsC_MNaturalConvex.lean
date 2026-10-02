-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvex
-- name    : DiscreteConvex_NetworkFlowsC_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:02:54.877976+00:00
-- url     : https://prove2.me/theorems/877e8e7a-c80d-48f8-91d4-fdf1310a6853
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is M$^\natural$-convex: its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunction

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.NetworkFlowsC


