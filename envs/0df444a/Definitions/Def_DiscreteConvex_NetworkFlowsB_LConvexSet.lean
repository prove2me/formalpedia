-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexSet
-- name    : DiscreteConvex_NetworkFlowsB_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:55.665168+00:00
-- url     : https://prove2.me/theorems/56813828-b776-4752-bfe6-aed7fd98596d
-- title:
--   LConvexSet
-- statement:
--   An L-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- An L-convex set. -/
def LConvexSet (D : Set (V → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (fun v => max (p v) (q v)) ∈ D ∧ (fun v => min (p v) (q v)) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.NetworkFlowsB


