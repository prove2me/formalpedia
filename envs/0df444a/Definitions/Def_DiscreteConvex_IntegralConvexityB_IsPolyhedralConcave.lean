-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConcave
-- name    : DiscreteConvex_IntegralConvexityB_IsPolyhedralConcave
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:04:14.399052+00:00
-- url     : https://prove2.me/theorems/55b9a74f-6af5-4d17-a8b9-81c01f3c9063
-- title:
--   Polyhedral concave function
-- statement:
--   $h$ with $\operatorname{hyp}h$ a convex polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedronSet
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Hypo

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.80, dual notion: a polyhedral concave
function, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `h` is **polyhedral concave** if `hyp h` is a convex polyhedron. -/
def IsPolyhedralConcave {V : Type*} [Fintype V] (h : (V → ℝ) → EReal) : Prop :=
  IsPolyhedronSet (Hypo h)

end DiscreteConvex.IntegralConvexityB


