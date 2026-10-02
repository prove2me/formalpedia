-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZR
-- name    : DiscreteConvex_MConvexFunctionsD_ZeroMZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:56:02.563859+00:00
-- url     : https://prove2.me/theorems/399e439d-ae88-45c9-974b-4f91a5ee19da
-- title:
--   ZeroMZR
-- statement:
--   The class $0M[\mathbb Z|\mathbb R\to\mathbb R]$: $0M[\mathbb R\to\mathbb R]$ functions with arg-min-integrality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IntegralPolyhedralFunction

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0M[Z|R→R]`: `0M[R→R]` functions with arg-min-integrality. -/
def ZeroMZR (f : (V → ℝ) → WithTop ℝ) : Prop := ZeroMR f ∧ IntegralPolyhedralFunction f

end DiscreteConvex.MConvexFunctionsD


