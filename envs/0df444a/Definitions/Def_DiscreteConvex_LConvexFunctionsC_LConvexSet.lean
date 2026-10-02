-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexSet
-- name    : DiscreteConvex_LConvexFunctionsC_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:06.696569+00:00
-- url     : https://prove2.me/theorems/29b2a33d-2193-4a6f-b508-de95c839f364
-- title:
--   LConvexSet
-- statement:
--   An L-convex set (redeclared from mission `21-ch05b-lconvexsets`).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- An L-convex set (redeclared from mission `21-ch05b-lconvexsets`). -/
def LConvexSet (D : Set (V → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (fun v => max (p v) (q v)) ∈ D ∧ (fun v => min (p v) (q v)) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.LConvexFunctionsC


