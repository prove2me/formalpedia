-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_ZeroMR
-- name    : DiscreteConvex_MConvexFunctionsE_ZeroMR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:35.042531+00:00
-- url     : https://prove2.me/theorems/e6d5850a-9803-4349-9dc3-db791ef3d988
-- title:
--   ZeroMR
-- statement:
--   The class $0M[\mathbb R\to\mathbb R]$: polyhedral M-convex, positively homogeneous functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_PosHomogeneous

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0M[R→R]`: polyhedral M-convex, positively homogeneous functions. -/
def ZeroMR (g : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR g ∧ PosHomogeneous g

end DiscreteConvex.MConvexFunctionsE


