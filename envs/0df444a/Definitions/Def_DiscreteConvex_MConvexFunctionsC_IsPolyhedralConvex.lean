-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedralConvex
-- name    : DiscreteConvex_MConvexFunctionsC_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:25:11.377242+00:00
-- url     : https://prove2.me/theorems/7d6b79a8-062f-42a7-b624-afe43637f6cf
-- title:
--   IsPolyhedralConvex
-- statement:
--   $g$ is **polyhedral convex**: its epigraph is a polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161-162, supporting Theorems 6.45, 6.47.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161-162, supporting Theorems 6.45, 6.47

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedron

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is polyhedral convex: its epigraph, viewed inside `(Option V) → R` (`none` the extra
value-coordinate), is a polyhedron. -/
def IsPolyhedralConvex (g : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedron (W := Option V) {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsC


