-- Prove2me | Definitions.Def_RBMSensitivity_Data_bDeriv
-- name    : RBMSensitivity_Data_bDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:26.424967+00:00
-- url     : https://prove2.me/theorems/384bd298-9431-4fbd-8109-ef002d4c0c81
-- title:
--   The Jacobian $b'(\alpha)$
-- statement:
--   The Jacobian $b':U\to\mathbb R^J$ of the drift.
--
--   It appears in the equation (2.8) of the derivative process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The Jacobian `b'(α) ∈ ℝ^J`: arXiv:1907.00472v2, §2.1, p.5. -/
noncomputable def Data.bDeriv {J : ℕ} (D : Data J) (α : ℝ) : E J :=
  deriv D.b α

end RBMSensitivity


