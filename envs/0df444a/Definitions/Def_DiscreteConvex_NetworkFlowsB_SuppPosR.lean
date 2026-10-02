-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_SuppPosR
-- name    : DiscreteConvex_NetworkFlowsB_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:42.638555+00:00
-- url     : https://prove2.me/theorems/8baed8ca-7526-46b2-813e-ea8a4341470b
-- title:
--   SuppPosR
-- statement:
--   The positive support, real-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The positive support, real-vector version. -/
noncomputable def SuppPosR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.NetworkFlowsB


