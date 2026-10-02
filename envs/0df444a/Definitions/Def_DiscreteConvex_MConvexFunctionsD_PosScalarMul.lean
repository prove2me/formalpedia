-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul
-- name    : DiscreteConvex_MConvexFunctionsD_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:51.545235+00:00
-- url     : https://prove2.me/theorems/50e76965-81ed-4a5d-9210-4c7fb7e06506
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real, $c\bullet\top=\top$ for $c\ne 0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Scalar multiple of an extended real by a nonnegative real, `c • ⊤ = ⊤` for `c ≠ 0`. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsD


