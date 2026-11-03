-- Prove2me | Definitions.Def_levy_foundations_covarianceMatrix
-- name    : levy_foundations_covarianceMatrix
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:24:05.212989+00:00
-- url     : https://prove2.me/theorems/d527fb4c-57e5-4fbb-8d76-5a6a73242bf0
-- title:
--   Finite covariance kernel matrix
-- statement:
--   The finite matrix of pairwise kernel time differences.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Representation/BochnerGaussian.lean#L38

import Mathlib.Analysis.Matrix.PosDef

namespace LevyFoundations
/-- The finite complex kernel matrix sampled from a function of differences. -/
noncomputable def covarianceMatrix {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ψ (t i - t j)
end LevyFoundations


