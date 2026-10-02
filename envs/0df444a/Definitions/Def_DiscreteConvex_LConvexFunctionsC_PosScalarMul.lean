-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_PosScalarMul
-- name    : DiscreteConvex_LConvexFunctionsC_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:31:46.34298+00:00
-- url     : https://prove2.me/theorems/c21a17bd-4648-4405-9db8-a47399746719
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Scalar multiple of an extended real by a nonnegative real. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsC


