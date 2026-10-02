-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPosR
-- name    : DiscreteConvex_NetworkFlowsC_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:47.611582+00:00
-- url     : https://prove2.me/theorems/73a87e06-9cf0-4595-9109-76974cb304e5
-- title:
--   SuppPosR
-- statement:
--   The positive support, real-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def SuppPosR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.NetworkFlowsC


