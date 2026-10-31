-- Prove2me | Definitions.Def_RBMSensitivity_Data_RDeriv
-- name    : RBMSensitivity_Data_RDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:28.311768+00:00
-- url     : https://prove2.me/theorems/8d239210-3c9c-4008-a19c-02f09ab30b99
-- title:
--   The Jacobian $R'(\alpha)$
-- statement:
--   The Jacobian $R':U\to\mathbb R^{J\times J}$ of the reflection matrix.
--
--   It appears in the equation (2.8) of the derivative process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.6

import Mathlib
import Definitions.Def_RBMSensitivity_Data_R
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The Jacobian `R'(α) ∈ ℝ^{J×J}`: arXiv:1907.00472v2, §2.1, p.6. Entrywise `deriv`. -/
noncomputable def Data.RDeriv {J : ℕ} (D : Data J) (α : ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of fun k i => deriv (fun β => D.R β k i) α

end RBMSensitivity


