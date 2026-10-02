-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
-- name    : DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:22:55.223313+00:00
-- url     : https://prove2.me/theorems/6bd2676d-d71b-4ac6-8972-7d24a11b41b8
-- title:
--   IsPolyhedralConvex
-- statement:
--   $f:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ is polyhedral convex: its epigraph is a polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `f : Rⱽ → R ∪ {+∞}` is polyhedral convex: its epigraph is a polyhedron. -/
def IsPolyhedralConvex (f : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedron (W := Option V)
    {p : Option V → ℝ | f (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.NetworkFlowsB


