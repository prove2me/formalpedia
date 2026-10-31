-- Prove2me | Definitions.Def_RBMSensitivity_Data_spanAlong
-- name    : RBMSensitivity_Data_spanAlong
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:46.064303+00:00
-- url     : https://prove2.me/theorems/c2b026f8-ce34-485a-9aa1-a85404640cec
-- title:
--   $\mathrm{span}[\bigcup_{u\in(s,t]}d(\alpha,h(u))]$
-- statement:
--   For a path $h$ and $0\le s<t$,
--   $$\mathrm{span}\Big[\bigcup_{u\in(s,t]}d(\alpha,h(u))\Big].$$
--
--   An increment of the correction term of the derivative process over $(s,t]$ must lie in this subspace.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 2.10, p.7; Definition 4.11, p.13

import Mathlib
import Definitions.Def_RBMSensitivity_Data_dCone
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `span[⋃_{u ∈ (s,t]} d(α, h(u))]`: arXiv:1907.00472v2, Definition 2.10, p.7, and Definition 4.11,
p.13. -/
def Data.spanAlong {J : ℕ} (D : Data J) (α : ℝ) (h : ℝ≥0 → E J) (s t : ℝ≥0) :
    Submodule ℝ (E J) :=
  Submodule.span ℝ (⋃ u ∈ Set.Ioc s t, (D.dCone α (h u) : Set (E J)))

end RBMSensitivity


