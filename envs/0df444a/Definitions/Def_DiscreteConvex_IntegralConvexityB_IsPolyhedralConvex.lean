-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConvex
-- name    : DiscreteConvex_IntegralConvexityB_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:04:06.210367+00:00
-- url     : https://prove2.me/theorems/ea8f3db4-de0f-42c6-90b9-d477e837fbe0
-- title:
--   Polyhedral convex function
-- statement:
--   $f$ with $\operatorname{epi}f$ a convex polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedronSet
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Epi

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.80: a polyhedral convex function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` is **polyhedral convex** if `epi f` is a convex polyhedron. -/
def IsPolyhedralConvex {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  IsPolyhedronSet (Epi f)

end DiscreteConvex.IntegralConvexityB


