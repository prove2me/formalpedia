-- Prove2me | Definitions.Def_BroadieKaya_SV_NoncentralChiSquare
-- name    : BroadieKaya_SV_NoncentralChiSquare
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:07:52.411721+00:00
-- url     : https://prove2.me/theorems/4fef3578-e1cc-4ff4-adbf-f1d812eacffe
-- title:
--   Real-degree noncentral chi-square and the explicit variance draw
-- statement:
--   For real $d>0$ and $\lambda\ge0$, draw $J\sim\operatorname{Poisson}(\lambda/2)$, then draw $Y\mid J\sim\operatorname{Gamma}(d/2+J,\text{scale }2)$. The marginal measure of $Y$ defines the noncentral chi-square law $\chi_d^{\prime2}(\lambda)$. Mathlib parameterizes gamma distributions by rate, so the code uses rate $1/2$.
--
--   For elapsed time $\Delta>0$ and $v\ge0$, define
--   $$c_\Delta=\frac{\sigma^2(1-e^{-\kappa\Delta})}{4\kappa},\qquad
--   \lambda_\Delta(v)=\frac{4\kappa e^{-\kappa\Delta}v}{\sigma^2(1-e^{-\kappa\Delta})}.$$
--   The explicit variance-draw measure is the image of $\chi_d^{\prime2}(\lambda_\Delta(v))$ under $y\mapsto c_\Delta y$, with $d=4\kappa\theta/\sigma^2$. This defines a sampling distribution independently of the SDE. It accommodates every positive real degree, including degrees at most one and the central case $v=0$.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.1, (8)–(10) and the Poisson representation paragraph, pp. 219–220 (PDF 3–4)

import Definitions.Def_BroadieKaya_SV_SquareRootProcesses

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


/-- Poisson-gamma mixture; Mathlib's second gamma parameter is RATE, hence 1/2. -/
def noncentralChiSquare (d lam : ℝ) : Measure ℝ :=
  (poissonMeasure (Real.toNNReal (lam/2))).bind
    (fun j : ℕ => gammaMeasure (d/2 + j) (1/2))

def varianceScale (p : CIRParameters) (Δ : ℝ) : ℝ :=
  p.sigma^2 * (1-Real.exp (-p.kappa*Δ)) / (4*p.kappa)

def noncentrality (p : CIRParameters) (Δ v : ℝ) : ℝ :=
  4*p.kappa*Real.exp (-p.kappa*Δ)*v /
    (p.sigma^2 * (1-Real.exp (-p.kappa*Δ)))

def varianceLaw (p : CIRParameters) (Δ v : ℝ) : Measure ℝ :=
  (noncentralChiSquare (degree p) (noncentrality p Δ v)).map
    (fun y => varianceScale p Δ * y)

end BroadieKaya.SV


