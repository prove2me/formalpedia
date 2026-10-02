-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
-- name    : DiscreteConvex_LConvexFunctionsD_ZeroLR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:03:52.243995+00:00
-- url     : https://prove2.me/theorems/1ae22658-8995-4694-813b-ebadc2dbe201
-- title:
--   ZeroLR
-- statement:
--   The class $0L[\mathbb R\to\mathbb R]$: polyhedral L-convex, positively homogeneous functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[R→R]`: polyhedral L-convex, positively homogeneous functions. -/
def ZeroLR (g : (V → ℝ) → WithTop ℝ) : Prop := SBFR g ∧ TRFR g ∧ PosHomogeneous g

end DiscreteConvex.LConvexFunctionsD


