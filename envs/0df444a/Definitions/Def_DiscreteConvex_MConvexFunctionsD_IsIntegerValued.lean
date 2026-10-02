-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValued
-- name    : DiscreteConvex_MConvexFunctionsD_IsIntegerValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:55.251544+00:00
-- url     : https://prove2.me/theorems/da2e1770-5b0b-4022-b59c-a914db2daf5a
-- title:
--   IsIntegerValued
-- statement:
--   $f : \mathbb Z^V \to \mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def IsIntegerValued (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, f x = ⊤ ∨ ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsD


