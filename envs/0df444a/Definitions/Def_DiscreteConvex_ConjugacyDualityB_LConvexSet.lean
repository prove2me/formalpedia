-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LConvexSet
-- name    : DiscreteConvex_ConjugacyDualityB_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:58.601253+00:00
-- url     : https://prove2.me/theorems/767f38e4-458f-462b-8de3-717b9bc691fc
-- title:
--   LConvexSet
-- statement:
--   An L-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- An L-convex set. -/
def LConvexSet (D : Set (V → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (fun v => max (p v) (q v)) ∈ D ∧ (fun v => min (p v) (q v)) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.ConjugacyDualityB


