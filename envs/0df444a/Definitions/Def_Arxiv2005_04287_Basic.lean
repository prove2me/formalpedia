-- Prove2me | Definitions.Def_Arxiv2005_04287_Basic
-- name    : Arxiv2005_04287_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T09:08:43.92409+00:00
-- url     : https://prove2.me/theorems/305ffc39-ed83-5093-bc57-1eb6bac30b50
-- title:
--   Speckle from fractal vasculature: power-law radii, echo maps, Burr, Lomax, log-amplitude and Pearson densities, speckle SNR
-- statement:
--   Objects of the Theory section and the Discussion of Parker and Poul (2020). Every density below is a function on $\mathbb{R}$. A density the paper states only for positive arguments is $0$ elsewhere, and a density $f$ defines the measure $f\,dx$ on $\mathbb{R}$.
--
--   1. **Vessel radii (eq. 7).** For $b>1$ and $a_{\min}>0$, the power-law density $p(a)=\frac{b-1}{a_{\min}}\left(\frac{a}{a_{\min}}\right)^{-b}$ for $a>a_{\min}$, and $0$ otherwise.
--   2. **Radius-to-echo maps (p. 7).** Amplitude $A[a]=A_0\sqrt{a-a_{\min}}$ and intensity $I(a)=I_0(a-a_{\min})$ for $a>a_{\min}$, both $0$ otherwise.
--   3. **Amplitude densities.** Eq. (9): $p[A]=\dfrac{2A\,a_{\min}^{b-1}(b-1)}{A_0^2\big((A/A_0)^2+a_{\min}\big)^b}$. Eq. (10): $p[A]=\dfrac{2A(b-1)}{\lambda^2\big((A/\lambda)^2+1\big)^b}$. Both are for $A>0$. The standard Burr XII density with shapes $c,k$ and scale $s$ is $\frac{ck}{s}(x/s)^{c-1}\big(1+(x/s)^c\big)^{-(k+1)}$ for $x>0$.
--   4. **Intensity densities.** Eq. (13): $p_I(I)=\dfrac{b-1}{a_{\min}^{1-b}I_0\,(I/I_0+a_{\min})^b}$. Eq. (14): $p_I(I)=\dfrac{(b-1)\lambda_2^{b-1}}{(I+\lambda_2)^b}$. Both are for $I>0$. The standard Lomax density with shape $\alpha$ and scale $s$ is $\frac{\alpha}{s}(1+x/s)^{-(\alpha+1)}$ for $x>0$.
--   5. **Log-amplitude density (eq. 15).** $p_y(y)=\dfrac{2(b-1)e^{2y}}{\lambda^2\big(e^{2y}/\lambda^2+1\big)^b}$ for every real $y$.
--   6. **Phase and in-phase component.** A uniform phase has law $\frac{1}{2\pi}\,d\theta$ on $[0,2\pi)$. Eq. (17) is the density $p(\hat A)=\dfrac{(b-1)\Gamma(b-\tfrac12)}{\sqrt\pi\,\Gamma(b)\,(1+\hat A^2)^{b-1/2}}$ for every real $\hat A$.
--   7. **Speckle SNR (p. 19).** For a law $\mu$ of the echo amplitude, $\mathrm{SNR}(\mu)=m/\sqrt{\int(x-m)^2\,d\mu}$ with $m=\int x\,d\mu$. The Rayleigh value is $\sqrt{\pi/(4-\pi)}=1.913\ldots$, printed as $1.91$.
--
--   **Formalization Note** The paper's parameter $\lambda$ is written `lam` and $\lambda_2$ is written `lam2`. Eq. (15) is defined for every real $y$, although the paper prints the range $y>0$ (see the statement for eq. (15)).
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1, Theory (eqs. (7)-(17), pp. 7-12; Table 1, p. 13) and Discussion (speckle SNR, p. 19)

import Mathlib

/-!
K. J. Parker and S. S. Poul, *Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound
Speckle*, arXiv:2005.04287v1 (2020): the power-law law of vessel radii (eq. (7)), the radius-to-echo
maps (Theory, "Spatial Convolutions and Transforms", p. 7), and the probability densities of the
echo amplitude (eqs. (9), (10)), intensity (eqs. (13), (14)), log amplitude (eq. (15)) and in-phase
component (eq. (17)), with the standard Burr XII and Lomax densities the paper identifies them
with and the speckle signal-to-noise ratio of the Discussion (p. 19).

Every density is a function `ℝ → ℝ`; a density stated by the paper only on a half-line is `0` off
it. A density `f` is turned into a measure on `ℝ` as `volume.withDensity (ENNReal.ofReal ∘ f)`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2005_04287

/-- Eq. (7), p. 7: the power-law density of vessel radii,
`p(a) = ((b - 1)/a_min) (a/a_min)^(-b)` for `a > a_min`, and `0` otherwise. -/
def powerLawDensity (b amin : ℝ) (a : ℝ) : ℝ :=
  if amin < a then ((b - 1) / amin) * (a / amin) ^ (-b) else 0

/-- Eq. (7), p. 7: the law of the radius `a` of the vessel met by the pulse, the measure on `ℝ`
with density `powerLawDensity b amin`. -/
def powerLawMeasure (b amin : ℝ) : Measure ℝ :=
  volume.withDensity (fun a => ENNReal.ofReal (powerLawDensity b amin a))

/-- P. 7 ("Spatial Convolutions and Transforms"): the echo amplitude of a cylinder of radius `a`,
`A[a] = A0 sqrt(a - a_min)` for `a > a_min`, and `0` otherwise. -/
def ampMap (A0 amin : ℝ) (a : ℝ) : ℝ :=
  if amin < a then A0 * Real.sqrt (a - amin) else 0

/-- P. 7 and p. 8 ("Probability of Intensity"): the average echo intensity of a cylinder of
radius `a`, `I(a) = I0 (a - a_min)` for `a > a_min`, and `0` otherwise. -/
def intensityMap (I0 amin : ℝ) (a : ℝ) : ℝ :=
  if amin < a then I0 * (a - amin) else 0

/-- Eq. (9), p. 8: the amplitude density
`p[A] = 2 A a_min^(b-1) (b - 1) / (A0^2 ((A/A0)^2 + a_min)^b)` for `A > 0`, and `0` otherwise. -/
def ampDensity9 (b amin A0 : ℝ) (A : ℝ) : ℝ :=
  if 0 < A then 2 * A * amin ^ (b - 1) * (b - 1) / (A0 ^ 2 * ((A / A0) ^ 2 + amin) ^ b) else 0

/-- Eq. (10), p. 8 (and Table 1, p. 13): the two-parameter amplitude density
`p[A] = 2 A (b - 1) / (lam^2 ((A/lam)^2 + 1)^b)` for `A > 0`, and `0` otherwise. -/
def burrDensity (b lam : ℝ) (A : ℝ) : ℝ :=
  if 0 < A then 2 * A * (b - 1) / (lam ^ 2 * ((A / lam) ^ 2 + 1) ^ b) else 0

/-- Eq. (10), p. 8: the law of the echo amplitude, the measure on `ℝ` with density
`burrDensity b lam`. -/
def burrMeasure (b lam : ℝ) : Measure ℝ :=
  volume.withDensity (fun A => ENNReal.ofReal (burrDensity b lam A))

/-- P. 8, refs. 45, 46: the standard Burr Type XII density with shape parameters `c`, `k` and
scale `s`, `f(x) = (c k / s) (x/s)^(c-1) (1 + (x/s)^c)^(-(k+1))` for `x > 0`, and `0` otherwise. -/
def burrXIIDensity (c k s : ℝ) (x : ℝ) : ℝ :=
  if 0 < x then (c * k / s) * (x / s) ^ (c - 1) * (1 + (x / s) ^ c) ^ (-(k + 1)) else 0

/-- Eq. (13), p. 9: the intensity density
`p_I(I) = (b - 1) / (a_min^(1-b) I0 (I/I0 + a_min)^b)` for `I > 0`, and `0` otherwise. -/
def intensityDensity13 (b amin I0 : ℝ) (I : ℝ) : ℝ :=
  if 0 < I then (b - 1) / (amin ^ (1 - b) * I0 * (I / I0 + amin) ^ b) else 0

/-- Eq. (14), p. 9 (and Table 1, p. 13): the intensity density
`p_I(I) = (b - 1) lam2^(b-1) / (I + lam2)^b` for `I > 0`, and `0` otherwise. -/
def intensityDensity14 (b lam2 : ℝ) (I : ℝ) : ℝ :=
  if 0 < I then (b - 1) * lam2 ^ (b - 1) / (I + lam2) ^ b else 0

/-- Eq. (14), p. 9: the law of the echo intensity, the measure on `ℝ` with density
`intensityDensity14 b lam2`. -/
def intensityMeasure (b lam2 : ℝ) : Measure ℝ :=
  volume.withDensity (fun I => ENNReal.ofReal (intensityDensity14 b lam2 I))

/-- P. 9, ref. 47: the standard Lomax (Pareto type II) density with shape `alpha` and scale `s`,
`f(x) = (alpha / s) (1 + x/s)^(-(alpha+1))` for `x > 0`, and `0` otherwise. -/
def lomaxDensity (alpha s : ℝ) (x : ℝ) : ℝ :=
  if 0 < x then (alpha / s) * (1 + x / s) ^ (-(alpha + 1)) else 0

/-- Eq. (15), p. 10 (and Table 1, p. 13): the log-amplitude density
`p_y(y) = 2 (b - 1) exp(2y) / (lam^2 (exp(2y)/lam^2 + 1)^b)`, as a function of every real `y`
(the paper prints the range `y > 0`; see the statement `logAmplitude_pdf`). -/
def logAmpDensity (b lam : ℝ) (y : ℝ) : ℝ :=
  2 * (b - 1) * Real.exp (2 * y) / (lam ^ 2 * (Real.exp (2 * y) / lam ^ 2 + 1) ^ b)

/-- Eq. (15), p. 10: the law of the log amplitude `y = ln A`, the measure on `ℝ` with density
`logAmpDensity b lam`. -/
def logAmpMeasure (b lam : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (logAmpDensity b lam y))

/-- P. 11 (text before eq. (17)): the law of a phase `theta` uniform on `[0, 2 pi)`, the measure
`(1/(2 pi)) * Lebesgue` restricted to `[0, 2 pi)`. -/
def uniformPhase : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ico 0 (2 * Real.pi))

/-- Eq. (17), p. 12 (and Table 1, p. 13): the density of the in-phase component `|A| cos theta_A`,
`p(x) = (b - 1) Gamma(b - 1/2) / (sqrt(pi) Gamma(b) (1 + x^2)^(b - 1/2))` for every real `x`. -/
def pearsonDensity (b : ℝ) (x : ℝ) : ℝ :=
  (b - 1) * Real.Gamma (b - 1 / 2) /
    (Real.sqrt Real.pi * Real.Gamma b * (1 + x ^ 2) ^ (b - 1 / 2))

/-- Eq. (17), p. 12: the law of the in-phase component, the measure on `ℝ` with density
`pearsonDensity b`. -/
def pearsonMeasure (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (pearsonDensity b x))

/-- P. 19 (Discussion, ref. 9): the speckle signal-to-noise ratio of a law `mu` of the echo
amplitude, its mean divided by its standard deviation. -/
def speckleSNR (mu : Measure ℝ) : ℝ :=
  (∫ x, x ∂mu) / Real.sqrt (∫ x, (x - ∫ x', x' ∂mu) ^ 2 ∂mu)

/-- P. 19 (ref. 9, Burckhardt 1978): the speckle signal-to-noise ratio of the Rayleigh amplitude
law, `sqrt(pi / (4 - pi)) = 1.913...`, printed in the paper as `1.91`. -/
def rayleighSNR : ℝ := Real.sqrt (Real.pi / (4 - Real.pi))

end Arxiv2005_04287


