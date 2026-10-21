-- Prove2me | Definitions.Def_SysRiskPortfolio_CoER_GaussianRisk
-- name    : SysRiskPortfolio_CoER_GaussianRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:06.993377+00:00
-- url     : https://prove2.me/theorems/10d56fc6-8803-4969-bf32-4edb9eb9d5d6
-- title:
--   (2.1), (A.1)–(A.2) — Gaussian quantiles, VaR and lower expected shortfall
-- statement:
--   For a real-valued law $\nu$, define its lower $q$-quantile by
--   $$\operatorname{VaR}_q(\nu)=\inf\{v:q\le\nu(({-}\infty,v])\}.$$
--   The standard normal cumulative distribution and density are $\Phi$ and $\phi$, and $\Phi^{-1}$ is the corresponding left quantile. Lower expected shortfall is $q^{-1}\int_{(-\infty,\operatorname{VaR}_q]}x\,d\nu(x)$.
--
--   These definitions supply the quantile and truncated expectation objects used in the paper's Gaussian calculations.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), pp. 5, 27, (2.1), (A.1)–(A.2)

import Mathlib

namespace SysRiskPortfolio.CoER

open MeasureTheory ProbabilityTheory

/-- Standard normal cumulative distribution function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Standard normal density. -/
noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- Left quantile of the standard normal law. -/
noncomputable def PhiInv (q : ℝ) : ℝ := sInf {t : ℝ | q ≤ Phi t}

/-- Left quantile of a real-valued law, as in (2.1). -/
noncomputable def VaR (nu : Measure ℝ) (q : ℝ) : ℝ :=
  sInf {v : ℝ | ENNReal.ofReal q ≤ nu (Set.Iic v)}

/-- Lower-tail expected shortfall, as in (A.2). -/
noncomputable def ES (nu : Measure ℝ) (q : ℝ) : ℝ :=
  (1 / q) * ∫ x in Set.Iic (VaR nu q), x ∂nu

end SysRiskPortfolio.CoER


