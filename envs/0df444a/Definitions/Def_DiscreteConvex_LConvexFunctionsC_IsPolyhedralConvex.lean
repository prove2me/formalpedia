-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex
-- name    : DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:35:36.277222+00:00
-- url     : https://prove2.me/theorems/f95a33d7-1fa9-423e-8f20-7bc5da61db90
-- title:
--   IsPolyhedralConvex
-- statement:
--   $g$ is polyhedral convex: its epigraph is a polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161-162, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161-162, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedron

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is polyhedral convex: its epigraph is a polyhedron. Murota, *Discrete Convex Analysis*,
SIAM 2003, §7.5 states Theorem 7.33 and Proposition 7.34 for polyhedral L-convex functions, not
for every function satisfying (SBF[R]) and (TRF[R]). -/
def IsPolyhedralConvex (g : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedron (W := Option V) {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.LConvexFunctionsC


