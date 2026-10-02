-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionR
-- name    : DiscreteConvex_NetworkFlowsC_LiftedFunctionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:48.660221+00:00
-- url     : https://prove2.me/theorems/abef6311-a94f-46f5-bdff-488d05d54c38
-- title:
--   LiftedFunctionR
-- statement:
--   The lift of $f$ to $\tilde V$, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def LiftedFunctionR (f : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.NetworkFlowsC


