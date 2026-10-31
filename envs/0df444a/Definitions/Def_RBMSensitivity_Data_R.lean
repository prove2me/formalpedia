-- Prove2me | Definitions.Def_RBMSensitivity_Data_R
-- name    : RBMSensitivity_Data_R
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:20.590092+00:00
-- url     : https://prove2.me/theorems/dc49a2c8-cdf7-4b67-93b1-743f3cf18652
-- title:
--   The reflection matrix $R(\alpha)$
-- statement:
--   The reflection matrix
--   $$R(\alpha):=\big(d_1(\alpha)\ \cdots\ d_J(\alpha)\big),$$
--   whose $i$th column is the direction of reflection on the $i$th face.
--
--   Under Assumption 2.2 it is invertible, which allows the constraining process to be decomposed along the faces.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, (2.4), p.6

import Mathlib
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The reflection matrix `R(α) := (d_1(α) ⋯ d_J(α))` of (2.4): arXiv:1907.00472v2, p.6. The `i`th
column is `d_i(α)`. -/
noncomputable def Data.R {J : ℕ} (D : Data J) (α : ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of fun k i => D.d i α k

end RBMSensitivity


