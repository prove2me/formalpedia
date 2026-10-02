-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet
-- name    : DiscreteConvex_LConvexFunctionsB_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:54.156985+00:00
-- url     : https://prove2.me/theorems/0261fcfa-fe3c-4a83-ba91-66c3a7348df5
-- title:
--   LConvexSet
-- statement:
--   An L-convex set (redeclared from mission `21-ch05b-lconvexsets`).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, real-variable analogue redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, real-variable analogue redeclared

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- An L-convex set (redeclared from mission `21-ch05b-lconvexsets`). -/
def LConvexSet (D : Set (V → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (fun v => max (p v) (q v)) ∈ D ∧ (fun v => min (p v) (q v)) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.LConvexFunctionsB


