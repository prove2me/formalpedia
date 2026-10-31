-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_ShiftedLaw
-- name    : QiFixedDesign_Concentration_ShiftedLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:49.086682+00:00
-- url     : https://prove2.me/theorems/15038ea8-f666-4b30-81e4-345d8dea3bfa
-- title:
--   Training-conditioned shifted innovation law
-- statement:
--   Fix an innovation law $\mu$, design sequence $x$, true coefficient $\beta_0$ and prediction vector $c$. For each realized training vector $\omega$, the shifted innovation law is the pushforward of $\mu$ by $u\mapsto u+(\beta_0-\widehat\beta_N(\omega))^T c$. The OLS estimator is calculated from that same training vector. The shift map is continuous for each realization. This is the conditional law of an independent future innovation after the fitted prediction error, rather than a mixture averaged over training data. In particular $c=0$ gives $\mu$.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, §3 following (13), PDF/printed p. 11

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_Design
import Definitions.Def_QiFixedDesign_Concentration_OLS
import Definitions.Def_QiFixedDesign_Concentration_Response

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def shiftedLaw {p N : ℕ} (μ : Measure ℝ) (x : ℕ → Fin p → ℝ)
    (β₀ c : Fin p → ℝ) (ω : Fin N → ℝ) : Measure ℝ :=
  μ.map (fun u => u + (β₀ - ols (designMatrix x N) (response x β₀ ω)) ⬝ᵥ c)

end QiFixedDesign.Concentration


