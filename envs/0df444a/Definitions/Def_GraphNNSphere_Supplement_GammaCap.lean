-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_GammaCap
-- name    : GraphNNSphere_Supplement_GammaCap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:45:15.230099+00:00
-- url     : https://prove2.me/theorems/393d12f4-3dd5-47b8-a0f9-4a906f414915
-- title:
--   Enrichment boundaries $\Gamma(\mu,\lambda)$ and $K_{\mathrm{cap}}(\mu,\lambda)$
-- statement:
--   For $\lambda>0$ and $\mu>0$ define
--
--   $$\Gamma(\mu,\lambda)=\lambda+\frac12\log\Big(1-e^{-2\mu}(1-e^{-2\lambda})^2\Big),\qquad K_{\mathrm{cap}}(\mu,\lambda)=\lambda+\mu+\frac12\log\Big(1-e^{-2\mu}(1-e^{-2\lambda})\Big).$$
--
--   A degree $e^{\gamma d}$ with $\gamma<\Gamma(\mu,\lambda)$ leaves too few stored edges to reach an enriched cap of density level $e^{\mu d}$ from all exterior entries, and $\kappa>K_{\mathrm{cap}}(\mu,\lambda)$ allows enough exterior points while keeping the log-density oscillation below $\kappa d$ (Theorem 4.8).
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §4.5, p.49

import Mathlib

namespace GraphNNSphere

namespace Supplement

/-- The degree boundary `Γ(μ, λ) = λ + ½ log(1 - e^{-2μ}(1 - e^{-2λ})²)` of the enrichment
construction (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.5, p.49). -/
noncomputable def GammaCap (μ lam : ℝ) : ℝ :=
  lam + Real.log (1 - Real.exp (-2 * μ) * (1 - Real.exp (-2 * lam)) ^ 2) / 2

/-- The required density variation `K_cap(μ, λ) = λ + μ + ½ log(1 - e^{-2μ}(1 - e^{-2λ}))`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.5, p.49). -/
noncomputable def Kcap (μ lam : ℝ) : ℝ :=
  lam + μ + Real.log (1 - Real.exp (-2 * μ) * (1 - Real.exp (-2 * lam))) / 2

end Supplement

end GraphNNSphere


