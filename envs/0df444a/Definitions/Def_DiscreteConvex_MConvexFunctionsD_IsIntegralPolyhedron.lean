-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegralPolyhedron
-- name    : DiscreteConvex_MConvexFunctionsD_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:24.756059+00:00
-- url     : https://prove2.me/theorems/945ffd36-87cd-423a-a199-f0679ba884be
-- title:
--   IsIntegralPolyhedron
-- statement:
--   A polyhedron equal to the convex hull of its integer points.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def IsIntegralPolyhedron (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.MConvexFunctionsD


