-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_PosScalarMul
-- name    : DiscreteConvex_ConjugacyDualityB_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:16.030978+00:00
-- url     : https://prove2.me/theorems/30114bd1-237c-4113-bd42-f45a43be6bf6
-- title:
--   PosScalarMul
-- statement:
--   Scalar multiple of an extended real by a nonnegative real.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Scalar multiple of an extended real by a nonnegative real. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityB


