-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_SubDifferentialR
-- name    : DiscreteConvex_NetworkFlowsB_SubDifferentialR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:13.208136+00:00
-- url     : https://prove2.me/theorems/bea5a7cc-be08-4487-ab4d-f4c72ba136f7
-- title:
--   SubDifferentialR
-- statement:
--   The real subdifferential of a real-domain function at a point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The (real) subdifferential of a real-domain function at a point. -/
def SubDifferentialR (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : Set (V → ℝ) :=
  {x : V → ℝ | ∀ q : V → ℝ, g q - g p ≥ (((∑ v, x v * (q v - p v)) : ℝ) : WithTop ℝ)}

end DiscreteConvex.NetworkFlowsB


