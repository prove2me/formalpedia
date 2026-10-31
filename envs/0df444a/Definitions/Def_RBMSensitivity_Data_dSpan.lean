-- Prove2me | Definitions.Def_RBMSensitivity_Data_dSpan
-- name    : RBMSensitivity_Data_dSpan
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:08.064782+00:00
-- url     : https://prove2.me/theorems/b751f6b7-6983-4d9d-a5e3-dc51301b9183
-- title:
--   The span $\mathrm{span}[d(\alpha,x)]$
-- statement:
--   The linear span $\mathrm{span}[d(\alpha,x)]$ of the cone $d(\alpha,x)$, with $\mathrm{span}(\emptyset):=\{0\}$.
--
--   The correction terms of the derivative problem live in this span, not in the cone, because linearization loses the sign constraint.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §4.3, (4.11), p.15

import Mathlib
import Definitions.Def_RBMSensitivity_Data_dCone
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `span[d(α, x)]`, as in (4.11): arXiv:1907.00472v2, §4.3, p.15. -/
def Data.dSpan {J : ℕ} (D : Data J) (α : ℝ) (x : E J) : Submodule ℝ (E J) :=
  Submodule.span ℝ (D.dCone α x : Set (E J))

end RBMSensitivity


