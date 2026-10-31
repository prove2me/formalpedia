-- Prove2me | Definitions.Def_RBMSensitivity_Data_sigma
-- name    : RBMSensitivity_Data_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:26.070157+00:00
-- url     : https://prove2.me/theorems/1a41ccf1-414d-4109-814a-623439675678
-- title:
--   The square root $\sigma(\alpha)$ of $a(\alpha)$
-- statement:
--   For $\alpha\in U$, $\sigma(\alpha)\in\mathbb M^{J\times J}$ is the unique positive definite symmetric square root of $a(\alpha)$, so that $a(\alpha)=\sigma(\alpha)(\sigma(\alpha))^T$.
--
--   It multiplies the Brownian motion in the equation of the RBM. It is continuously differentiable because $a$ is, so $\sigma$ is a derived object and not an additional datum.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace RBMSensitivity

/-- `σ(α) ∈ M^{J×J}`, the unique positive definite square root of `a(α)`, so that
`a(α) = σ(α)(σ(α))^T`: arXiv:1907.00472v2, §2.1, p.5.

**Formalization Note.** It is defined as `CFC.sqrt` of `a(α)`. No smoothness of `σ` is assumed: the
paper derives it from that of `a`, so it is a fact about this definition, and not a hypothesis. -/
noncomputable def Data.sigma {J : ℕ} (D : Data J) (α : ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  CFC.sqrt (D.a α)

end RBMSensitivity


