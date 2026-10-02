-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_PosScalarMul
-- name    : DiscreteConvex_MConvexFunctionsE_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:01.671715+00:00
-- url     : https://prove2.me/theorems/c2475a42-02f6-4ec6-965a-aea013a48f39
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real, $c\bullet\top=\top$ for $c\ne 0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Scalar multiple of an extended real by a nonnegative real, `c • ⊤ = ⊤` for `c ≠ 0`. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsE


