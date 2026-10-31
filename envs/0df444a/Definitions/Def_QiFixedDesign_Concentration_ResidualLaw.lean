-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_ResidualLaw
-- name    : QiFixedDesign_Concentration_ResidualLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:57.027773+00:00
-- url     : https://prove2.me/theorems/697a01ca-ea81-4e4d-a1e1-d55643fe3133
-- title:
--   Residual empirical distribution and its OLS fit
-- statement:
--   For coefficients $\beta_0,\beta\in\mathbb R^p$, the residual empirical distribution is $\widehat P_N(\beta)=N^{-1}\sum_{i=1}^N\delta_{Y_i-\beta^T x_i}$, where $Y_i=\beta_0^T x_i+\omega_i$. Its fitted version substitutes the concrete OLS coefficient $(X_N^T X_N)^{-1}X_N^T Y$. It uses the published uniform empirical measure. Positive admissible sample sizes are imposed by the theorems. The residuals are not assumed independent or identically distributed.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, §3, (13), PDF/printed pp. 10–11

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_Design
import Definitions.Def_QiFixedDesign_Concentration_OLS
import Definitions.Def_QiFixedDesign_Concentration_Response
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def residualLaw {p N : ℕ} (x : ℕ → Fin p → ℝ)
    (β₀ β : Fin p → ℝ) (ω : Fin N → ℝ) : Measure ℝ :=
  WassersteinDRO.Duality.empiricalDistribution (fun i => response x β₀ ω i - β ⬝ᵥ x i.val)

noncomputable def fittedResidualLaw {p N : ℕ} (x : ℕ → Fin p → ℝ)
    (β₀ : Fin p → ℝ) (ω : Fin N → ℝ) : Measure ℝ :=
  residualLaw x β₀ (ols (designMatrix x N) (response x β₀ ω)) ω

end QiFixedDesign.Concentration


