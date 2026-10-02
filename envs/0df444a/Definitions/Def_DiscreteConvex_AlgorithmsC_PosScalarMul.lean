-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_PosScalarMul
-- name    : DiscreteConvex_AlgorithmsC_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:58.287671+00:00
-- url     : https://prove2.me/theorems/7c4d449b-d1b3-48a0-afe5-7a8041c2d7cd
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Scalar multiple of an extended real by a nonnegative real. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.AlgorithmsC


