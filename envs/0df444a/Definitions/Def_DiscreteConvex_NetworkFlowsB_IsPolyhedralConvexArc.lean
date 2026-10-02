-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
-- name    : DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:07.374459+00:00
-- url     : https://prove2.me/theorems/5858fe9c-a51b-48e9-b807-6370a51a7774
-- title:
--   IsPolyhedralConvexArc
-- statement:
--   A univariate function $g:\mathbb R\to\mathbb R\cup\{+\infty\}$ is polyhedral convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80, univariate specialization.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80, univariate specialization

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate function `g : R → R ∪ {+∞}` is polyhedral convex. -/
def IsPolyhedralConvexArc (g : ℝ → WithTop ℝ) : Prop :=
  IsPolyhedron (W := Bool) {p : Bool → ℝ | g (p false) ≤ ((p true : ℝ) : WithTop ℝ)}

end DiscreteConvex.NetworkFlowsB


