-- Prove2me | Definitions.Def_BroadieKaya_SV_BesselContinuation
-- name    : BroadieKaya_SV_BesselContinuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:06:51.851343+00:00
-- url     : https://prove2.me/theorems/abc1ea74-76a7-4926-b908-88278ddbb718
-- title:
--   The entire Bessel factor and the continued endpoint ratio
-- statement:
--   For real $\nu>-1$ and $z\in\mathbb C$, put
--   $$H_\nu(z)=\sum_{j=0}^{\infty}\frac{(z^2/4)^j}{j!\Gamma(\nu+j+1)}.$$
--   Equation (21) writes $I_\nu(z)=(z/2)^\nu H_\nu(z)$. For a nonnegative endpoint factor $h$, the ratio $I_\nu(hq)/I_\nu(hq_0)$ is encoded as
--   $$e^{\nu L}\,H_\nu(hq)/H_\nu(hq_0),$$
--   where $L$ is the continuous logarithm of $q/q_0$. For positive real $q,q_0$ this is $(q/q_0)^\nu H_\nu(hq)/H_\nu(hq_0)$. At $h=0$ the entire factors cancel, retaining the power ratio instead of evaluating an undefined quotient of Bessel values.
--
--   The squared Bessel bridge expression is
--   $$\frac{bt}{\sinh(bt)}e^{\frac{x+y}{2t}(1-bt\coth(bt))}
--   \frac{I_{n/2-1}(\sqrt{xy}\,b/\sinh(bt))}{I_{n/2-1}(\sqrt{xy}/t)}.$$
--   The code uses the cancelled ratio at zero endpoints and defines the removable value at $b=0$ to be one. The dimension $n$ and parameter $b$ are real.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.2, (21)–(22), p. 221 (PDF 5); Appendix, (39), pp. 229–230 (PDF 13–14)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


/-- The entire factor in (21), for real order ν > -1 and complex argument. -/
def besselH (ν : ℝ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, (z^2/4)^j / ((j.factorial : ℂ) * (Real.Gamma (ν+j+1) : ℂ))

/-- First-kind Bessel ratio after cancelling the common zero-endpoint power.
L is the continued logarithm of the ratio q/q₀. -/
def continuedBesselRatio (ν h : ℝ) (q q₀ L : ℂ) : ℂ :=
  Complex.exp ((ν : ℂ)*L) * besselH ν ((h : ℂ)*q) / besselH ν ((h : ℂ)*q₀)

/-- Real positive argument ratio with its zero-endpoint extension. -/
def realBesselRatio (ν h q q₀ : ℝ) : ℝ :=
  (q/q₀)^ν * (besselH ν ((h*q : ℝ) : ℂ)).re /
    (besselH ν ((h*q₀ : ℝ) : ℂ)).re

/-- Removable b=0 values are explicit; real b may have either sign. -/
def besselBridgeTransform (n t x y b : ℝ) : ℝ :=
  if b = 0 then 1 else
    (b*t / Real.sinh (b*t)) *
      Real.exp ((x+y)/(2*t) * (1-b*t*Real.cosh (b*t)/Real.sinh (b*t))) *
      realBesselRatio (n/2-1) (Real.sqrt (x*y)) (b/Real.sinh (b*t)) (1/t)

end BroadieKaya.SV


