-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegralPolyhedron
-- name    : DiscreteConvex_NetworkFlowsB_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:58.861438+00:00
-- url     : https://prove2.me/theorems/d9f696dd-2882-44ef-844a-4eea2c59faba
-- title:
--   IsIntegralPolyhedron
-- statement:
--   A polyhedron $P\subseteq\mathbb R^V$ is integral if it coincides with the convex hull of the integer points it contains.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A polyhedron `P ⊆ Rⱽ` is integral if it coincides with the convex hull of the integer points
it contains. -/
def IsIntegralPolyhedron (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.NetworkFlowsB


