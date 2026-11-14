-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_WitnessRate
-- name    : KSATSingleFlip_Connect_WitnessRate
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T06:43:28.471778+00:00
-- url     : https://prove2.me/theorems/73af6103-a4d5-459c-ac20-25ccf6c615a6
-- title:
--   Binary entropy and witness exponential rate
-- statement:
--   The binary entropy is $H(b)=-b\ln b-(1-b)\ln(1-b)$, with $0\ln0=0$. The witness exponential-rate function is $$\Psi_\beta(a,b)=a(1-\ln a)+H(b)-\frac\beta2(a+b)^2+a\ln(e^{a+b}-1)+(a+b)[\ln\beta+(\beta^{-1}-1)\ln(1-\beta)].$$ These are the functions preceding Lemma 8.11 in the pinned paper.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Section 8.2, printed p. 71 (PDF p. 73), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib

noncomputable section
namespace KSATSingleFlip.Connect

/-- Binary entropy H, with the endpoint convention 0 log 0 = 0. -/
def witnessEntropy (b : ℝ) : ℝ :=
  - b * Real.log b - (1 - b) * Real.log (1 - b)

/-- Exponential-rate function Ψβ(a,b) in Section 8.2 of the pinned paper. -/
def witnessRate (β a b : ℝ) : ℝ :=
  a * (1 - Real.log a) + witnessEntropy b - β / 2 * (a + b)^2 +
    a * Real.log (Real.exp (a + b) - 1) +
    (a + b) * (Real.log β + (β⁻¹ - 1) * Real.log (1 - β))

end KSATSingleFlip.Connect


