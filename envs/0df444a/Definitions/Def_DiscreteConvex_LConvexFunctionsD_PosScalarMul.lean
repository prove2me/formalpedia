-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosScalarMul
-- name    : DiscreteConvex_LConvexFunctionsD_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:01.539988+00:00
-- url     : https://prove2.me/theorems/34b8c7d6-88af-45b3-a45f-8c5c9364f82e
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Scalar multiple of an extended real by a nonnegative real. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


