-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_SubDifferentialArc
-- name    : DiscreteConvex_NetworkFlowsB_SubDifferentialArc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:15.568858+00:00
-- url     : https://prove2.me/theorems/08a95736-63ae-4420-89a6-ce778e6c6e51
-- title:
--   SubDifferentialArc
-- statement:
--   The real subdifferential of a univariate function at a point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, redeclared, univariate.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, redeclared, univariate

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The (real) subdifferential of a univariate function at a point. -/
def SubDifferentialArc (g : ℝ → WithTop ℝ) (t : ℝ) : Set ℝ :=
  {s : ℝ | ∀ t' : ℝ, g t' - g t ≥ (((s * (t' - t)) : ℝ) : WithTop ℝ)}

end DiscreteConvex.NetworkFlowsB


