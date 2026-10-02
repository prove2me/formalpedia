-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsIntegralPolyhedron
-- name    : DiscreteConvex_MConvexFunctionsE_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:54.928982+00:00
-- url     : https://prove2.me/theorems/d19d8ea9-a1d3-4561-8006-c5227f9802b3
-- title:
--   IsIntegralPolyhedron
-- statement:
--   A polyhedron equal to the convex hull of its integer points.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A polyhedron equal to the convex hull of its integer points. -/
def IsIntegralPolyhedron (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.MConvexFunctionsE


