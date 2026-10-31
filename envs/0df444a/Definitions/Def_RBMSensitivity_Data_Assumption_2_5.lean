-- Prove2me | Definitions.Def_RBMSensitivity_Data_Assumption_2_5
-- name    : RBMSensitivity_Data_Assumption_2_5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:52.259974+00:00
-- url     : https://prove2.me/theorems/4e18ed33-da46-4d93-8132-2271f245af91
-- title:
--   Assumption 2.5: a projection onto $G$
-- statement:
--   **Assumption 2.5.** For each $\alpha\in U$ there is a function $\pi^\alpha:\mathbb R^J\to G$ satisfying $\pi^\alpha(x)=x$ for all $x\in G$ and $\pi^\alpha(x)-x\in d(\alpha,\pi^\alpha(x))$ for all $x\notin G$.
--
--   It is the assumption used for the existence of RBMs.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Assumption 2.5, p.6

import Mathlib
import Definitions.Def_RBMSensitivity_Data_dCone
import Definitions.Def_RBMSensitivity_SimpleCone_G
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Assumption 2.5: arXiv:1907.00472v2, p.6. For each `α ∈ U` there is `π^α : ℝ^J → G` with
`π^α(x) = x` for `x ∈ G` and `π^α(x) - x ∈ d(α, π^α(x))` for `x ∉ G`. -/
def Data.Assumption_2_5 {J : ℕ} (D : Data J) : Prop :=
  ∀ α ∈ D.U, ∃ π : E J → E J, (∀ x, π x ∈ D.G) ∧ (∀ x ∈ D.G, π x = x) ∧
    ∀ x, x ∉ D.G → π x - x ∈ D.dCone α (π x)

end RBMSensitivity


