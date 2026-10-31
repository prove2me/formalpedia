-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsDerivProj
-- name    : RBMSensitivity_Data_IsDerivProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:10.02983+00:00
-- url     : https://prove2.me/theorems/e30f77f6-c5fa-4669-a08b-4e1293c92af1
-- title:
--   Derivative projection operators $\mathcal L_x^\alpha$
-- statement:
--   For $\alpha\in U$ and $x\in\partial G$, the **derivative projection operator** $\mathcal L_x^\alpha:\mathbb R^J\to\mathbb R^J$ is the unique function such that for each $y\in\mathbb R^J$,
--   $$\mathcal L_x^\alpha y\in\mathbb H_x\qquad\text{and}\qquad\mathcal L_x^\alpha y-y\in\mathrm{span}[d(\alpha,x)].$$
--
--   Such operators describe what the derivative process does when the RBM reaches the boundary. They are the projections through which the contraction of the derivative process acts.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Lemma 4.18, (4.11), p.15

import Mathlib
import Definitions.Def_RBMSensitivity_Data_dSpan
import Definitions.Def_RBMSensitivity_SimpleCone_H
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The defining property (4.11) of the derivative projection operator `L_x^α`: arXiv:1907.00472v2,
Lemma 4.18, p.15. For each `y`, `L y ∈ H_x` and `L y - y ∈ span[d(α, x)]`. Lemma 4.18 says exactly one
such function exists for `x ∈ ∂G`, and that it is linear. -/
def Data.IsDerivProj {J : ℕ} (D : Data J) (α : ℝ) (x : E J) (L : E J → E J) : Prop :=
  ∀ y, L y ∈ D.H x ∧ L y - y ∈ D.dSpan α x

end RBMSensitivity


