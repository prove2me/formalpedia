-- Prove2me | Definitions.Def_RBMSensitivity_Data_coneAlong
-- name    : RBMSensitivity_Data_coneAlong
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:55.201994+00:00
-- url     : https://prove2.me/theorems/c467fee9-4678-49bc-95ee-6587a9ac3ddd
-- title:
--   $\mathrm{cone}[\bigcup_{u\in(s,t]}d(\alpha,h(u))]$
-- statement:
--   For a path $h$ and $0\le s<t$,
--   $$\mathrm{cone}\Big[\bigcup_{u\in(s,t]}d(\alpha,h(u))\Big].$$
--
--   An increment of the constraining term over $(s,t]$ must lie in this cone. This is the **extended** form of the Skorokhod condition, which does not presuppose bounded variation.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 2.1, p.5; Definition 4.1, p.11

import Mathlib
import Definitions.Def_RBMSensitivity_Data_dCone
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `cone[⋃_{u ∈ (s,t]} d(α, h(u))]`: arXiv:1907.00472v2, Definition 2.1, p.5, and Definition 4.1,
p.11. The union is over the half-open interval `(s, t]`. -/
def Data.coneAlong {J : ℕ} (D : Data J) (α : ℝ) (h : ℝ≥0 → E J) (s t : ℝ≥0) :
    PointedCone ℝ (E J) :=
  PointedCone.hull ℝ (⋃ u ∈ Set.Ioc s t, (D.dCone α (h u) : Set (E J)))

end RBMSensitivity


