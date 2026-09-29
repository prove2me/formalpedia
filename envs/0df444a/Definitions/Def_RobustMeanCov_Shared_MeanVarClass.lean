-- Prove2me | Definitions.Def_RobustMeanCov_Shared_MeanVarClass
-- name    : RobustMeanCov_Shared_MeanVarClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:43:08.226977+00:00
-- url     : https://prove2.me/theorems/1763c8e3-cf4f-4db3-af4b-8fbb3bc7edad
-- title:
--   The class $\mathbb{M}_{(m,v)}$ of laws on $\mathbb{R}$ with mean $m$ and variance $v$
-- statement:
--   For real numbers $m$ and $v$, the class $\mathbb{M}_{(m,v)}$ is the set of Borel probability measures $\nu$ on $\mathbb{R}$ with finite second moment, mean $m$ and variance $v$:
--
--   $$
--   \int r\, d\nu(r) = m, \qquad \int (r-m)^2\, d\nu(r) = v .
--   $$
--
--   It is the univariate case ($n=1$) of the mean-covariance class $\mathbb{M}^n_{(\mu,\Sigma)}$. A random variable $r$ with law in $\mathbb{M}_{(m,\sigma^2)}$ is what the paper writes $r\sim(m,\sigma^2)$. For a vector $x$ the relevant instance is $\mathbb{M}_{(\mu_x,\sigma_x^2)}$ with $\mu_x = x'\mu$ and $\sigma_x^2 = x'\Sigma x$; by Proposition 1 the robust objective of $x$ is an infimum over this class.
--
--   Used by two missions of this paper: 01-projection (the target class of the projection property, p. 100, §2.1 after Proposition 1, "with the default superscript $n=1$"; p. 99, §1) and 03-one-point-support (the class over which the robust objective is taken, p. 100, §2.1–§2.2, notation $r\sim(\mu_x,\sigma_x^2)$).
--
--   **Formalization Note** The second parameter is the variance $v=\sigma^2$ itself, as in the paper's subscript $(\mu_x,\sigma_x^2)$, not the standard deviation; statements with a standard deviation $s\ge0$ use it as `MeanVarClass m (s ^ 2)`. The finite-second-moment clause (`MemLp … 2`) keeps the Bochner integrals from taking Lean's default value $0$ on heavy-tailed laws. For $v<0$ the class is empty.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 100, §2.1, after Proposition 1 ('with the default superscript n = 1') and §2.2 (notation r ∼ (μ_x, σ_x²)); p. 99, §1 ('univariate distributions r_x with given mean μ_x = x′μ and variance σ_x² = x′Σx')

import Mathlib
open MeasureTheory

namespace RobustMeanCov.Shared

/-- The univariate class `𝕄_(m,v)` (Popescu 2007, p. 100, "with the default superscript
`n = 1`"): probability measures `ν` on `ℝ` with finite second moment, mean `m` and variance `v`.
The second parameter is the variance `v = σ²`, as in the paper's subscript `(μ_x, σ_x²)`. -/
def MeanVarClass (m v : ℝ) : Set (Measure ℝ) :=
  {ν | IsProbabilityMeasure ν ∧ MemLp (fun r : ℝ => r) 2 ν ∧
    ∫ r, r ∂ν = m ∧ ∫ r, (r - m) ^ 2 ∂ν = v}

end RobustMeanCov.Shared


