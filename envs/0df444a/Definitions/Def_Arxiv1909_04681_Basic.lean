-- Prove2me | Definitions.Def_Arxiv1909_04681_Basic
-- name    : Arxiv1909_04681_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T06:47:55.575719+00:00
-- url     : https://prove2.me/theorems/42f85406-72bd-5d83-be86-eb87706333a6
-- title:
--   Phase distribution, von Mises distribution, concentration parameter and Bessel functions of the closure-phase approximation
-- statement:
--   Objects of Sections 2-3 and Appendices A-B of Christian and Psaltis (arXiv:1909.04681v2).
--
--   1. **Error functions.** $\operatorname{Erf}x=\frac{2}{\sqrt\pi}\int_0^xe^{-t^2}\,dt$ and $\operatorname{Erfc}x=1-\operatorname{Erf}x$.
--   2. **Modified Bessel functions (eq. 34).** For an integer $n\ge0$ and real $z$, $I_n(z)=\left(\tfrac z2\right)^n\sum_{k\ge0}\frac{(z^2/4)^k}{k!\,(n+k)!}$. The coefficient of $z^j$ in this series is $C_{j,n}=2^{-j}\left[\left(\tfrac{j-n}{2}\right)!\left(\tfrac{j+n}{2}\right)!\right]^{-1}$ when $j=n+2k$ with $k\in\mathbb N$ (eqs. 35-36), and $C_{j,n}=0$ for every other integer $j$. The ansatz of eq. (38) is $\tilde I_4(z)=A\,I_0(z)+B\,I_1(z)/z+C\,I_0(z)/z^2+D\,I_1(z)/z^3$.
--   3. **Phase distribution of one baseline (eq. 1).** For visibility amplitude $V$, noise $\sigma$ and $\mathrm{SNR}=V/\sigma$,
--   $$P(\phi)=\frac{e^{-\mathrm{SNR}^2/2}}{4\pi\sigma}\Big(\sqrt{2\pi}\,\mathrm{SNR}\cos\phi\,e^{\mathrm{SNR}^2\cos^2\phi/2}\big\{\operatorname{Erf}[\mathrm{SNR}\cos\phi/\sqrt2]+1\big\}+2\Big),$$
--   exactly as printed.
--   4. **Von Mises density (eq. 3).** $\mathrm{vM}(\mu,\kappa,x)=e^{\kappa\cos(x-\mu)}/(2\pi I_0(\kappa))$.
--   5. **Curvature ratio (eqs. 4, 8).** For a function with expansion $f(\phi)=f_0+f_2\phi^2+O(\phi^3)$ at $0$, the ratio $f_2/f_0$, where $f_0=f(0)$ and $f_2=f''(0)/2$.
--   6. **Concentration parameter (eqs. 13, 14).** $\kappa(\mathrm{SNR})=-\dfrac{\mathrm{SNR}}{\sqrt{2\pi}\,\mathrm{SNR}\,e^{\mathrm{SNR}^2/2}[\operatorname{Erf}(\mathrm{SNR}/\sqrt2)+1]+2}\Big\{-2\,\mathrm{SNR}+\sqrt{2\pi}\,e^{\mathrm{SNR}^2/2}(1+\mathrm{SNR}^2)[\operatorname{Erfc}(\mathrm{SNR}/\sqrt2)-2]\Big\}$, and its approximation $\kappa_{\approx}(\mathrm{SNR})=\dfrac{\sqrt{\pi/2}\,\mathrm{SNR}}{1+\sqrt{\pi/2}\,\mathrm{SNR}}+\mathrm{SNR}^2$.
--   7. **Closure phase (eqs. 22, 24, 25).** The convolution $G(x)=\int_0^{2\pi}\!\int_0^{2\pi}\mathrm{vM}(\mu_1,\kappa_1,\theta)\,\mathrm{vM}(\mu_2,\kappa_2,\phi-\theta)\,\mathrm{vM}(\mu_3,\kappa_3,x-\phi)\,d\theta\,d\phi$; the printed coefficients $\tilde G_n=\dfrac{I_n(\kappa_1)I_n(\kappa_2)I_n(\kappa_3)}{(2\pi)^3I_0(\kappa_1)I_0(\kappa_2)I_0(\kappa_3)}$; and the printed mixture distribution $\tfrac{1}{(2\pi)^3}+\sum_{n\ge1}2\tilde G_n\cos[n(x-c_0)]$, $c_0=\mu_1+\mu_2+\mu_3$.
--   8. **Noise-dominated approximation (eq. 30).** $P_a(\phi)=\frac1{2\pi}+\frac{\mathrm{SNR}}{\sqrt{8\pi}}\cos\phi$.
--
--   **Formalization Note** Eqs. (24) and (25) print $I_n(\kappa_1)$ twice and omit $I_n(\kappa_2)$; the definitions use $I_n(\kappa_1)I_n(\kappa_2)I_n(\kappa_3)$. Eq. (1) is kept with the printed prefactor $1/(4\pi\sigma)$, although it integrates to $1/\sigma$ over a period; the only statement that uses it (eq. 13) involves only the ratio $P_2/P_0$, which does not depend on the prefactor. $C_{j,n}$ is defined as the actual coefficient of $z^j$, so it vanishes when $j<n$ or $j-n$ is odd, where the printed formula (36) is not meaningful.
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), Section 2 (eqs. 1, 3, 4-14), Section 3 (eqs. 22-25), Appendix A (eq. 30), Appendix B (eqs. 34-38)

import Mathlib

/-!
Christian and Psaltis, *Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise
Ratio Regime*, arXiv:1909.04681v2 (2020): the single-baseline phase distribution (eq. 1), the von
Mises distribution (eq. 3), the moment-matched concentration parameter (eqs. 4-13) and its
approximation (eq. 14) of Section 2; the triple convolution and the mixture distribution
(eqs. 22-25) of Section 3; the noise-dominated approximation (eq. 30) of Appendix A; and the
modified Bessel functions of the first kind with their series coefficients (eqs. 34-38) of
Appendix B.
-/

noncomputable section

namespace Arxiv1909_04681

open Real

/-- The error function `Erf`, used in eqs. (1), (5)-(7) and (13):
`Erf x = (2 / √π) ∫₀ˣ e^{-t²} dt`. -/
def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The complementary error function `Erfc x = 1 - Erf x`, used in eqs. (7) and (13). -/
def erfc (x : ℝ) : ℝ := 1 - erf x

/-- Appendix B, eq. (34): the modified Bessel function of the first kind of integer order `n ≥ 0`,
`I_n(z) = (z/2)^n ∑_{k ≥ 0} (z²/4)^k / (k! (n+k)!)` (the series converges for every real `z`). -/
def besselI (n : ℕ) (z : ℝ) : ℝ :=
  (z / 2) ^ n * ∑' k : ℕ, (z ^ 2 / 4) ^ k / ((Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ))

/-- Appendix B, eqs. (35)-(36): `C_{j,n}`, the coefficient of `z^j` in the power series of `I_n`,
equal to `2^{-j} [((j-n)/2)! ((j+n)/2)!]^{-1}` when `j = n + 2k` for some `k ∈ ℕ`, and `0` for
every other integer `j` (no such power occurs in the series). -/
def besselCoeff (j : ℤ) (n : ℕ) : ℝ :=
  if (n : ℤ) ≤ j ∧ Even (j - n) then
    1 / ((2 : ℝ) ^ j.toNat * ((Nat.factorial ((j - n) / 2).toNat : ℝ) *
      (Nat.factorial ((j + n) / 2).toNat : ℝ)))
  else 0

/-- Appendix B, eq. (38): the ansatz `Ĩ₄(z) = A I₀(z) + B I₁(z)/z + C I₀(z)/z² + D I₁(z)/z³`. -/
def besselI4Tilde (A B C D z : ℝ) : ℝ :=
  A * besselI 0 z + B * besselI 1 z / z + C * besselI 0 z / z ^ 2 + D * besselI 1 z / z ^ 3

/-- Section 2, eq. (1): the phase distribution `P(φ)` of a single baseline with visibility
amplitude `V` and noise `σ`, `SNR = V/σ`, exactly as printed (prefactor `e^{-SNR²/2}/(4πσ)`):
`P(φ) = e^{-SNR²/2}/(4πσ) · (√(2π) SNR cos φ e^{SNR² cos² φ / 2} {Erf[SNR cos φ/√2] + 1} + 2)`. -/
def truePhaseDensity (V σ phi : ℝ) : ℝ :=
  Real.exp (-(V / σ) ^ 2 / 2) / (4 * Real.pi * σ) *
    (Real.sqrt (2 * Real.pi) * (V / σ) * Real.cos phi *
        Real.exp ((V / σ) ^ 2 * Real.cos phi ^ 2 / 2) *
        (erf ((V / σ) * Real.cos phi / Real.sqrt 2) + 1) + 2)

/-- Section 2, eq. (3): the von Mises density with location `μ` and concentration `κ`,
`vM(μ, κ, x) = e^{κ cos(x - μ)} / (2π I₀(κ))`. -/
def vonMises (μ κ x : ℝ) : ℝ :=
  Real.exp (κ * Real.cos (x - μ)) / (2 * Real.pi * besselI 0 κ)

/-- Section 2, eqs. (4), (7), (8), (11): for an expansion `f(φ) = f₀ + f₂ φ² + O(φ³)` at `φ = 0`,
the ratio `f₂ / f₀` of the second-order to the zeroth-order coefficient, with the Taylor
coefficients `f₀ = f(0)` and `f₂ = f''(0)/2`. -/
def curvatureRatio (f : ℝ → ℝ) : ℝ :=
  (iteratedDeriv 2 f 0 / 2) / f 0

/-- Section 2, eq. (13): the moment-matched von Mises concentration parameter `κ(SNR)`,
`κ = -SNR / {√(2π) SNR e^{SNR²/2} [Erf(SNR/√2) + 1] + 2}
      × {-2 SNR + √(2π) e^{SNR²/2} (1 + SNR²) [Erfc(SNR/√2) - 2]}`. -/
def kappaOfSNR (S : ℝ) : ℝ :=
  -(S / (Real.sqrt (2 * Real.pi) * S * Real.exp (S ^ 2 / 2) * (erf (S / Real.sqrt 2) + 1) + 2)) *
    (-2 * S + Real.sqrt (2 * Real.pi) * Real.exp (S ^ 2 / 2) * (1 + S ^ 2) *
      (erfc (S / Real.sqrt 2) - 2))

/-- Section 2, eq. (14): the approximation
`κ(SNR) ≈ √(π/2) SNR / (1 + √(π/2) SNR) + SNR²`. -/
def kappaApprox (S : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 2) * S / (1 + Real.sqrt (Real.pi / 2) * S) + S ^ 2

/-- Section 3, eq. (22): the convolution of three von Mises densities,
`G(x) = ∫₀^{2π} ∫₀^{2π} vM(μ₁,κ₁,θ) vM(μ₂,κ₂,φ-θ) vM(μ₃,κ₃,x-φ) dθ dφ`. -/
def vonMisesTripleConv (μ₁ μ₂ μ₃ κ₁ κ₂ κ₃ x : ℝ) : ℝ :=
  ∫ phi in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
    vonMises μ₁ κ₁ θ * vonMises μ₂ κ₂ (phi - θ) * vonMises μ₃ κ₃ (x - phi)

/-- Section 3, eq. (24), as printed with the repeated factor `I_n(κ₁)` read as `I_n(κ₂)`:
`G̃_n = I_n(κ₁) I_n(κ₂) I_n(κ₃) / ((2π)³ I₀(κ₁) I₀(κ₂) I₀(κ₃))`, for `n ≥ 0`. -/
def mixtureFourierCoeff (κ₁ κ₂ κ₃ : ℝ) (n : ℕ) : ℝ :=
  besselI n κ₁ * besselI n κ₂ * besselI n κ₃ /
    ((2 * Real.pi) ^ 3 * (besselI 0 κ₁ * besselI 0 κ₂ * besselI 0 κ₃))

/-- Section 3, eq. (25), the mixture distribution as printed (with `I_n(κ₂)` for the repeated
`I_n(κ₁)`): `1/(2π)³ + ∑_{n ≥ 1} G̃_n · 2 cos[n(x - c₀)]`, with `c₀ = μ₁ + μ₂ + μ₃`. -/
def mixtureDensity (μ₁ μ₂ μ₃ κ₁ κ₂ κ₃ x : ℝ) : ℝ :=
  1 / (2 * Real.pi) ^ 3 +
    ∑' n : ℕ, mixtureFourierCoeff κ₁ κ₂ κ₃ (n + 1) *
      (2 * Real.cos (((n + 1 : ℕ) : ℝ) * (x - (μ₁ + μ₂ + μ₃))))

/-- Appendix A, eq. (30): the noise-dominated approximation of the phase distribution,
`P_a(φ) = 1/(2π) + SNR cos φ / √(8π)`. -/
def noiseApprox (S phi : ℝ) : ℝ :=
  1 / (2 * Real.pi) + S / Real.sqrt (8 * Real.pi) * Real.cos phi

end Arxiv1909_04681


