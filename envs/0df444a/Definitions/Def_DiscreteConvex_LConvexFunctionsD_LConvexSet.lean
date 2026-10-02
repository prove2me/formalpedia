-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexSet
-- name    : DiscreteConvex_LConvexFunctionsD_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:40.882719+00:00
-- url     : https://prove2.me/theorems/fd362309-f551-456c-9779-2a9967455175
-- title:
--   LConvexSet
-- statement:
--   An L-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- An L-convex set. -/
def LConvexSet (D : Set (V → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (fun v => max (p v) (q v)) ∈ D ∧ (fun v => min (p v) (q v)) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.LConvexFunctionsD


