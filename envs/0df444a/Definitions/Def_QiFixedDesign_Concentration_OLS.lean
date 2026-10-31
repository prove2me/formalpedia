-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_OLS
-- name    : QiFixedDesign_Concentration_OLS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:04.158487+00:00
-- url     : https://prove2.me/theorems/19f0b326-9867-4b69-a54d-c919ec7b08e0
-- title:
--   Ordinary least squares coefficient
-- statement:
--   For a real $N\times p$ matrix $X$ and a response vector $Y$, define the ordinary least squares coefficient by $\widehat\beta=(X^T X)^{-1}X^T Y$. The formula is used only when $X^T X$ is nonsingular. This definition is separate from the paper-specific response model; it has no stochastic assumptions. The total matrix inverse outside this domain is not an assertion about regression.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, (13), PDF/printed p. 11

import Mathlib

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def ols {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ)
    (Y : Fin N → ℝ) : Fin p → ℝ :=
  (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ Y)

end QiFixedDesign.Concentration


