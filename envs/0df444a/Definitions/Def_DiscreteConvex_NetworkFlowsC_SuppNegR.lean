-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNegR
-- name    : DiscreteConvex_NetworkFlowsC_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:48.611199+00:00
-- url     : https://prove2.me/theorems/d6f429a5-57f5-4624-83d3-458281877cd1
-- title:
--   SuppNegR
-- statement:
--   The negative support, real-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def SuppNegR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.NetworkFlowsC


