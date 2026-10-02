-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsMZeroR
-- name    : DiscreteConvex_MConvexFunctionsE_IsMZeroR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:48.318136+00:00
-- url     : https://prove2.me/theorems/2013d3fd-0adc-40f9-a4fc-cf80b08ffc9b
-- title:
--   IsMZeroR
-- statement:
--   The class $M_0[\mathbb R]$: real M-convex polyhedral cones, realized as the effective domain of an M-convex indicator function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167-168, class $M_0[\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167-168, class $M_0[\\mathbb R]$

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IndicatorR

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `M0[R]`: real M-convex polyhedral cones, realized as the effective domain of an
M-convex indicator function. -/
def IsMZeroR (P : Set (V → ℝ)) : Prop := MExchangeAxiomR (IndicatorR P)

end DiscreteConvex.MConvexFunctionsE


