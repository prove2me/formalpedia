-- Prove2me | Definitions.Def_SysRiskPortfolio_CoER_BivariateNormal
-- name    : SysRiskPortfolio_CoER_BivariateNormal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:42.375981+00:00
-- url     : https://prove2.me/theorems/734ee812-a3b3-45fe-8809-a9cdb99b2247
-- title:
--   (2.2)–(2.3), Assumption 2 — bivariate normal conditional law, CoVaR and CoER=
-- statement:
--   Let $(X,Y)$ have a bivariate normal density with means $\mu_x,\mu_y$, standard deviations $\sigma_x,\sigma_y$, and correlation $\rho$. Define the density of $X$ at $x$ conditional on $Y=y$ as its joint density at $(x,y)$ divided by the integral of that joint density over $x$.
--
--   The **conditional value at risk** $\operatorname{CoVaR}_{q_p}$ is the lower $q_p$-quantile of this conditional law at the system value $y=\operatorname{VaR}_{q_m}(Y)$. The **co-expected return** is its mean below CoVaR:
--   $$\operatorname{CoER}^{=}=\frac{\int_{(-\infty,\operatorname{CoVaR}_{q_p}]}x\,d\nu_y(x)}{\nu_y(({-}\infty,\operatorname{CoVaR}_{q_p}])}.$$
--
--   **Formalization Note** Conditioning at an exact Gaussian value uses the density ratio, which fixes a continuous version of the conditional law. The denominator is the actual conditional probability; its equality to $q_p$ is a mathematical result.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), pp. 5–7, 27–28, (2.2)–(2.3), Assumption 2, (A.3)–(A.4)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_GaussianRisk

namespace SysRiskPortfolio.CoER

open MeasureTheory ProbabilityTheory

/-- Density of a nondegenerate bivariate Gaussian with marginal standard deviations sx, sy. -/
noncomputable def bvnPDF (mux muy sx sy rho x y : ℝ) : ℝ :=
  let zx := (x - mux) / sx
  let zy := (y - muy) / sy
  (1 / (2 * Real.pi * sx * sy * Real.sqrt (1 - rho ^ 2))) *
    Real.exp (-(zx ^ 2 - 2 * rho * zx * zy + zy ^ 2) / (2 * (1 - rho ^ 2)))

/-- Conditional density of X given Y=y, formed as joint density divided by Y's marginal density. -/
noncomputable def condPDF (mux muy sx sy rho y x : ℝ) : ℝ :=
  bvnPDF mux muy sx sy rho x y / ∫ t : ℝ, bvnPDF mux muy sx sy rho t y

/-- The density-ratio version of the conditional law of X given Y=y. -/
noncomputable def condLaw (mux muy sx sy rho y : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (condPDF mux muy sx sy rho y x))

/-- CoVaR from (2.2): a quantile under the conditional law at the system's VaR. -/
noncomputable def CoVaR (mup mum sp sm rho qm qp : ℝ) : ℝ :=
  VaR (condLaw mup mum sp sm rho (VaR (gaussianReal mum ⟨sm ^ 2, sq_nonneg sm⟩) qm)) qp

/-- CoER= from (2.3): a conditional lower-tail expectation at the system's VaR. -/
noncomputable def CoER (mup mum sp sm rho qm qp : ℝ) : ℝ :=
  let law := condLaw mup mum sp sm rho
    (VaR (gaussianReal mum ⟨sm ^ 2, sq_nonneg sm⟩) qm)
  let c := CoVaR mup mum sp sm rho qm qp
  (∫ x in Set.Iic c, x ∂law) / (law (Set.Iic c)).toReal

end SysRiskPortfolio.CoER


