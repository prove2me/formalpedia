-- Prove2me | Definitions.Def_Arxiv1906_02603_Basic
-- name    : Arxiv1906_02603_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T06:40:17.688269+00:00
-- url     : https://prove2.me/theorems/b51e1223-d8e3-40b5-9c33-75c4a4c4e33e
-- title:
--   Echo energy, vessel power law, amplitude histogram and Burr density (Parker 2019)
-- statement:
--   Objects of Sections II, IV, V and the Appendix of Parker (2019), *The first order statistics of backscatter from the fractal branching vasculature*.
--
--   1. **Bessel function.** $J_1(x)=\frac1\pi\int_0^\pi\cos(\tau-x\sin\tau)\,d\tau$, the Bessel function of the first kind of order one (Bessel's integral).
--   2. **Echo of one cylinder (eq. 6).** For beam widths $\sigma_x,\sigma_y,\sigma_z$ and compressibility contrast $\kappa_0$, the echo energy of a long cylinder of radius $a$ perpendicular to the propagation direction is the right-hand side of eq. (6),
--   $$E(a)=\sigma_z^2\kappa_0^2\iint_{\mathbb{R}^2}\Big(8e^{-\pi^2(k_x^2\sigma_x^2+2k_y^2\sigma_y^2)}k_x^2\pi^{7/2}\sigma_x^3\sigma_y\Big)^2(k_x^2)^2\Big(\frac{a}{\sqrt{k_x^2+k_y^2}}J_1\big(2a\pi\sqrt{k_x^2+k_y^2}\big)\Big)^2dk_x\,dk_y,$$
--   and the RMS echo amplitude is $\sqrt{E(a)}$.
--   3. **Vessel population and amplitude map.** The number density of vessels of radius $a$ is $N[a]=N_0a^{-b}$, and the envelope amplitude of a vessel of radius $a>a_{\min}$ is $A[a]=A_0\sqrt{a-a_{\min}}$.
--   4. **Histograms.** The amplitude histogram (eq. 8) is $N[A]=\dfrac{2N_0A}{A_0^2[(A/A_0)^2+a_{\min}]^b}$; its normalization (eq. 9) is $N_n[A]=\dfrac{2A\,a_{\min}^{b-1}(b-1)}{A_0^2[(A/A_0)^2+a_{\min}]^b}$.
--   5. **Burr density (eq. 10).** With $\lambda=A_0\sqrt{a_{\min}}$, $N_n[A]=\dfrac{2A(b-1)}{\lambda^2[(A/\lambda)^2+1]^b}$. The Burr Type XII density with shapes $c,k$ and scale $\lambda$ is $f(x)=\frac{ck}{\lambda}(x/\lambda)^{c-1}(1+(x/\lambda)^c)^{-(k+1)}$.
--   6. **Moments, SNR and CDF (eqs. 11-14).** $\langle A^n\rangle=\int_0^\infty A^nN_n[A]\,dA$, $\mathrm{SNR}=\langle A\rangle/\sqrt{\langle A^2\rangle-\langle A\rangle^2}$, and $\mathrm{CDF}(A)=1-[1+(A/\lambda)^2]^{-(b-1)}$.
--   7. **Rayleigh density (eq. 15).** $R[A]=\frac{A}{S^2}e^{-A^2/(2S^2)}$.
--   8. **Appendix example.** The envelope $y=A_1(1-x^2)$ and the function $f(y)=1/\big(2A_1\sqrt{1-y/A_1}\big)$.
--
--   **Formalization Note** The paper uses $J_1$ without defining it; Mathlib has no Bessel functions, so $J_1$ is defined by Bessel's integral (Abramowitz and Stegun 9.1.21). The integral in eq. (6) is a Lebesgue integral over $\mathbb{R}^2$; its integrand is integrable for $\sigma_x,\sigma_y>0$. Real powers $x^b$ are `Real.rpow`, and the definitions are total; they are evaluated at nonpositive bases only off the relevant domains (e.g. on null sets of a measure, or away from the limit point), so only values at positive bases affect the statements.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), Section II eqs. (4)-(13), Section IV eqs. (14)-(15), Appendix eq. (16) and example, pp. 5-21

import Mathlib

/-!
K. J. Parker, *The first order statistics of backscatter from the fractal branching vasculature*,
arXiv:1906.02603v3 (2019): the RMS echo of a cylinder (Section II, eqs. (4)-(6)), the power-law
vessel population and its amplitude histogram (Section II, eqs. (7)-(13)), the Burr CDF and the
Rayleigh density (Section IV, eqs. (14)-(15)), and the envelope example of the Appendix
(eq. (16) and the example after it).
-/

open MeasureTheory

noncomputable section

namespace Arxiv1906_02603

/-- The Bessel function of the first kind of order one, `J₁`, used in the cylinder transform of
eq. (4) (Section II, p. 6), given by Bessel's integral
`J₁(x) = (1/π) ∫₀^π cos(τ - x sin τ) dτ` (Abramowitz and Stegun 9.1.21, cited by the paper). -/
def besselJ1 (x : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ τ in (0 : ℝ)..Real.pi, Real.cos (τ - x * Real.sin τ)

/-- Section II, eqs. (3), (5), (6) (pp. 5, 8): the factor
`8 exp[-π²(k_x² σ_x² + 2 k_y² σ_y²)] k_x² π^{7/2} σ_x³ σ_y` of eq. (6), i.e. the spatial Fourier
transform of the GH2 pulse with Gaussian beam profiles, evaluated at `k_z = 0` with the factor
`σ_z` taken out. -/
def pulseFactor (sx sy kx ky : ℝ) : ℝ :=
  8 * Real.exp (-(Real.pi ^ 2 * (kx ^ 2 * sx ^ 2 + 2 * ky ^ 2 * sy ^ 2))) * kx ^ 2 *
    Real.pi ^ ((7 : ℝ) / 2) * sx ^ 3 * sy

/-- Section II, eqs. (4)-(6) (pp. 6, 8): the cylinder factor
`a · (1/√(k_x²+k_y²)) · J₁(2 a π √(k_x²+k_y²))` of a cylinder of radius `a` (its 2D transform
`F(ρ) = κ₀ a J₁(2π a ρ)/ρ` with `κ₀` taken out). -/
def cylinderFactor (a kx ky : ℝ) : ℝ :=
  a * (1 / Real.sqrt (kx ^ 2 + ky ^ 2)) * besselJ1 (2 * a * Real.pi * Real.sqrt (kx ^ 2 + ky ^ 2))

/-- Section II, eq. (6) (p. 8): the echo energy of one long cylinder of radius `a` perpendicular
to the propagation direction, defined as the right-hand side of eq. (6),
`σ_z² κ₀² ∬ (pulse factor)² (k_x²)² (cylinder factor)² dk_x dk_y` over `ℝ²`. -/
def echoEnergy (sx sy sz kappa0 a : ℝ) : ℝ :=
  sz ^ 2 * kappa0 ^ 2 *
    ∫ k : ℝ × ℝ, pulseFactor sx sy k.1 k.2 ^ 2 * (k.1 ^ 2) ^ 2 * cylinderFactor a k.1 k.2 ^ 2

/-- Section II, text after eq. (6) (p. 8): the RMS echo amplitude, the square root of the echo
energy of eq. (6), as a function of the cylinder radius `a`. -/
def rmsEcho (sx sy sz kappa0 a : ℝ) : ℝ :=
  Real.sqrt (echoEnergy sx sy sz kappa0 a)

/-- Section II, p. 10 (and Section I, p. 4): the power-law number density of vessels of radius
`a`, `N[a] = N₀ / a^b`. -/
def vesselDensity (N0 b a : ℝ) : ℝ :=
  N0 * a ^ (-b)

/-- Section II, p. 10: the square-root map from cylinder radius to envelope amplitude,
`A[a] = A₀ √(a - a_min)` for `a > a_min`. -/
def amplitudeOfRadius (A0 amin a : ℝ) : ℝ :=
  A0 * Real.sqrt (a - amin)

/-- Section II, eq. (8) (p. 10): the histogram of envelope amplitudes
`N[A] = 2 N₀ A / (A₀² [(A/A₀)² + a_min]^b)`. -/
def ampHist (N0 A0 amin b A : ℝ) : ℝ :=
  2 * N0 * A / (A0 ^ 2 * ((A / A0) ^ 2 + amin) ^ b)

/-- Section II, eq. (9) (p. 11): the normalized histogram
`N_n[A] = 2 A a_min^{b-1} (b-1) / (A₀² [(A/A₀)² + a_min]^b)`. -/
def normHist (A0 amin b A : ℝ) : ℝ :=
  2 * A * amin ^ (b - 1) * (b - 1) / (A0 ^ 2 * ((A / A0) ^ 2 + amin) ^ b)

/-- Section II, p. 11: the scale parameter `λ = A₀ √a_min` of eq. (10). -/
def burrScale (A0 amin : ℝ) : ℝ :=
  A0 * Real.sqrt amin

/-- Section II, eq. (10) (p. 11): the two-parameter density
`N_n[A] = 2 A (b-1) / (λ² [(A/λ)² + 1]^b)`. -/
def burrPdf (lam b A : ℝ) : ℝ :=
  2 * A * (b - 1) / (lam ^ 2 * ((A / lam) ^ 2 + 1) ^ b)

/-- Section II, p. 11: the Burr Type XII density with shape parameters `c, k` and scale `λ`
(Burr 1942; Rodriguez 1977, cited by the paper),
`f(x) = (c k / λ) (x/λ)^{c-1} (1 + (x/λ)^c)^{-(k+1)}` for `x > 0`. -/
def burrXIIPdf (c k lam x : ℝ) : ℝ :=
  c * k / lam * (x / lam) ^ (c - 1) * (1 + (x / lam) ^ c) ^ (-(k + 1))

/-- Section II, eqs. (11)-(12) (p. 12): the `n`-th moment `⟨Aⁿ⟩ = ∫₀^∞ Aⁿ N_n[A] dA` of the
density of eq. (10). -/
def burrMoment (lam b : ℝ) (n : ℕ) : ℝ :=
  ∫ A in Set.Ioi (0 : ℝ), A ^ n * burrPdf lam b A

/-- Section II, eq. (13) (p. 12): the signal-to-noise ratio `SNR = ⟨A⟩ / σ_A` of the density of
eq. (10), the mean over the standard deviation, with `σ_A² = ⟨A²⟩ - ⟨A⟩²`. -/
def burrSNR (lam b : ℝ) : ℝ :=
  burrMoment lam b 1 / Real.sqrt (burrMoment lam b 2 - burrMoment lam b 1 ^ 2)

/-- Section IV, eq. (14) (p. 15): the Burr cumulative distribution function
`CDF(A) = 1 - [1 + (A/λ)²]^{-(b-1)}`. -/
def burrCdf (lam b A : ℝ) : ℝ :=
  1 - (1 + (A / lam) ^ 2) ^ (-(b - 1))

/-- Section IV, eq. (15) (p. 16): the Rayleigh density `R[A] = (A/S²) exp(-A²/(2S²))`. -/
def rayleighPdf (S A : ℝ) : ℝ :=
  A / S ^ 2 * Real.exp (-(A ^ 2 / (2 * S ^ 2)))

/-- Appendix, example after eq. (16) (p. 20): the envelope `y = A₁ (1 - x²)`. -/
def appendixEnvelope (A1 x : ℝ) : ℝ :=
  A1 * (1 - x ^ 2)

/-- Appendix, example after eq. (16) (p. 21): the histogram of the sampled envelope,
`f(y) = 1 / (2 A₁ √(1 - y/A₁))` for `0 < y < A₁`. -/
def appendixHist (A1 y : ℝ) : ℝ :=
  1 / (2 * A1 * Real.sqrt (1 - y / A1))

end Arxiv1906_02603


