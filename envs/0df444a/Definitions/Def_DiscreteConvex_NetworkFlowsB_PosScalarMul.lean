-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_PosScalarMul
-- name    : DiscreteConvex_NetworkFlowsB_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:12.148701+00:00
-- url     : https://prove2.me/theorems/e7d84870-4718-482b-809c-68dc84434a35
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Scalar multiple of an extended real by a nonnegative real. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


