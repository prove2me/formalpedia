-- Prove2me | Definitions.Def_RBMSensitivity_Data_sigmaDeriv
-- name    : RBMSensitivity_Data_sigmaDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:59.76998+00:00
-- url     : https://prove2.me/theorems/185541fe-1860-4537-a32e-1f2e52c42acb
-- title:
--   The Jacobian $\sigma'(\alpha)$
-- statement:
--   The Jacobian $\sigma':U\to\mathbb R^{J\times J}$ of $\sigma$.
--
--   It appears in the equation (2.8) of the derivative process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_Data_sigma
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The Jacobian `σ'(α) ∈ ℝ^{J×J}`: arXiv:1907.00472v2, §2.1, p.5.

**Formalization Note.** Entrywise `deriv`. `U` is open and `σ` is C¹ on `U`, so for `α ∈ U` this is
the true derivative. -/
noncomputable def Data.sigmaDeriv {J : ℕ} (D : Data J) (α : ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of fun i j => deriv (fun β => D.sigma β i j) α

end RBMSensitivity


