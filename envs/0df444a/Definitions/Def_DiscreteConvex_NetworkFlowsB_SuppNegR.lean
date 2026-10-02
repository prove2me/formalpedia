-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_SuppNegR
-- name    : DiscreteConvex_NetworkFlowsB_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:45.224544+00:00
-- url     : https://prove2.me/theorems/7cf6722e-9230-41a3-8da4-44fa9443f345
-- title:
--   SuppNegR
-- statement:
--   The negative support, real-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The negative support, real-vector version. -/
noncomputable def SuppNegR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.NetworkFlowsB


