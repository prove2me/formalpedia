-- Prove2me | Definitions.Def_Arxivcond_mat_0408414_Basic
-- name    : Arxivcond_mat_0408414_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:23:50.817927+00:00
-- url     : https://prove2.me/theorems/73cd6242-a016-4c05-b516-6eac1b350655
-- title:
--   Gaussian self-affine surfaces, the Kirchhoff mean DRC and the Lévy stable density
-- statement:
--   Objects of Simonsen, Vandembroucq and Roux, Secs. II-IV. Angles are in radians and the vacuum wave number is $\omega/c=2\pi/\lambda$.
--
--   1. **Slope over a distance (Eq. 3b).** For a self-affine profile with Hurst exponent $H$ and topothesy $\ell$, $s(\Delta x)=(\ell/\Delta x)^{1-H}$. The slope over one wavelength is $s(\lambda)$.
--   2. **Increment standard deviation (Eq. 4).** $\sigma(\Delta x)=\lambda\,s(\lambda)\,(\Delta x/\lambda)^H$ for $\Delta x\ge0$. With $s(\lambda)=(\ell/\lambda)^{1-H}$ this equals $\ell^{1-H}\Delta x^H$ (Eq. 3a).
--   3. **The function $\Omega$ (Eqs. 6, 14b, 15).** For angles $\theta_0,\theta$ let $Q=\frac{2\pi}{\lambda}(\cos\theta+\cos\theta_0)$. The increment over the horizontal distance $|v|$ is centred Gaussian with standard deviation $\sigma(|v|)$, and
--   $$\Omega(v)=\int_{\mathbb R}e^{-iQz}\,dN\big(0,\sigma(|v|)^2\big)(z).$$
--   When $\sigma=0$ the law is the point mass at $0$.
--   4. **Kirchhoff mean differential reflection coefficient for a profile of length $L$ (Eq. 14a).** For a function $\Omega$,
--   $$\Big\langle\frac{\partial R_s}{\partial\theta}\Big\rangle_L=\frac{1}{\lambda\cos\theta_0}\Big(\frac{\cos\frac{\theta+\theta_0}{2}}{\cos\frac{\theta-\theta_0}{2}}\Big)^2\int_{-L/2}^{L/2}e^{i\frac{2\pi}{\lambda}(\sin\theta-\sin\theta_0)v}\,\Omega(v)\,dv .$$
--   The factor $\frac{1}{\lambda}$ is the paper's $\frac{\omega}{2\pi c}$.
--   5. **Lévy stable density (Eq. 17c).** $\mathcal L_\alpha(x)=\frac{1}{2\pi}\int_{\mathbb R}e^{ikx}e^{-|k|^\alpha}\,dk$. The integral is real; its real part is taken.
--   6. **Closed form (Eqs. 17a, 17b).** With $a=2\pi\sqrt2\cos\frac{\theta+\theta_0}{2}\cos\frac{\theta-\theta_0}{2}$, the prefactor is
--   $$P=\frac{s^{-1/H}a^{-(1/H-1)}}{\sqrt2\cos\theta_0}\,\frac{\cos\frac{\theta+\theta_0}{2}}{\cos^3\frac{\theta-\theta_0}{2}},$$
--   the argument is $X=\dfrac{\sqrt2\tan\frac{\theta-\theta_0}{2}}{a^{1/H-1}s^{1/H}}$, and $\mathrm{mdrc}(H,s,\theta,\theta_0)=P\,\mathcal L_{2H}(X)$.
--   7. **Scaling lengths (Sec. IV).** $\delta_{ang}=\lambda/(\sin\theta-\sin\theta_0)$, $\delta_{rough}=\lambda s^{-1/H}/(\cos\theta+\cos\theta_0)^{1/H}$, and $\chi=\delta_{rough}/\delta_{ang}$.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Electromagnetic wave scattering from conducting self-affine surfaces: an analytic and numerical study, arXiv:cond-mat/0408414v2, Sec. II, Eqs. (3), (4), (6), PDF pp. 4-5; Sec. III, Eqs. (14a)-(15), (17a)-(17c), PDF pp. 7-8; Sec. IV, PDF p. 13

import Mathlib

/-!
I. Simonsen, D. Vandembroucq and S. Roux, *Electromagnetic wave scattering from conducting
self-affine surfaces: an analytic and numerical study*, arXiv:cond-mat/0408414v2: the
self-affine height-increment scales (Sec. II, Eqs. (3), (4)), the Gaussian increment law and the
function `Ω(v)` (Eqs. (6), (14b), (15)), the Kirchhoff mean differential reflection coefficient of a
profile of length `L` (Eq. (14a)), the centred symmetric Lévy stable density (Eq. (17c)), the
closed form (17a)-(17b) of the mean differential reflection coefficient, and the characteristic
lengths `δ_ang`, `δ_rough` and their ratio `χ` of the scaling analysis (Sec. IV).

Angles are in radians; the vacuum wave number is `ω/c = 2π/λ` (Sec. II-III).
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace Arxivcond_mat_0408414

/-- Sec. II, Eq. (3b), PDF p. 4: the mean slope of a self-affine profile of Hurst exponent `H`
and topothesy `ℓ` over a horizontal distance `Δx`, `s(Δx) = (ℓ/Δx)^(1-H)`. The slope over one
wavelength is `s(λ) = slope ℓ H λ`. -/
def slope (ell H dx : ℝ) : ℝ := (ell / dx) ^ (1 - H)

/-- Sec. II, Eq. (4), PDF p. 4: the standard deviation of the height increment
`ζ(x + Δx) - ζ(x)` over a horizontal distance `Δx ≥ 0`, normalised by the wavelength `λ`:
`σ(Δx) = λ s(λ) (Δx/λ)^H`, where `s = s(λ)` is the slope over one wavelength. -/
def incStd (lam s H dx : ℝ) : ℝ := lam * s * (dx / lam) ^ H

/-- Sec. III, Eqs. (14b) and (15) (first line), PDF p. 7, with the Gaussian law of Eq. (6):
`Ω(v) = ⟨exp{-i Q Δζ(v)}⟩ = ∫ exp(-i Q z) p(z; |v|) dz`, where `Q = (ω/c)(cos θ + cos θ₀)`,
`Q = (2π/λ)(cos θ + cos θ₀)`, and the increment `Δζ(v) = ζ(x) - ζ(x + v)` over the horizontal
distance `|v|` is centred Gaussian with standard deviation `σ(|v|) = incStd λ s H |v|`
(Eq. (6); stationary increments). The law is Mathlib's `gaussianReal 0 σ²`, which is the Dirac
mass at `0` when `σ = 0`. -/
def gaussOmega (lam s H θ θ0 : ℝ) (v : ℝ) : ℂ :=
  ∫ z, Complex.exp (-(((2 * π / lam) * (cos θ + cos θ0) * z : ℝ) : ℂ) * Complex.I)
    ∂(gaussianReal 0 ⟨(incStd lam s H |v|) ^ 2, sq_nonneg _⟩)

/-- Sec. III, Eq. (14a), PDF p. 7: the mean differential reflection coefficient in the Kirchhoff
approximation for a profile of length `L`, in terms of the function `Ω(v)` of Eq. (14b), with
`ω/c = 2π/λ`:
`⟨∂R_s/∂θ⟩ = (ω/(2πc)) (1/cos θ₀) (cos((θ+θ₀)/2)/cos((θ-θ₀)/2))²
  ∫_{-L/2}^{L/2} exp{i (ω/c)(sin θ - sin θ₀) v} Ω(v) dv`. -/
def kirchhoffMDRC (lam θ θ0 L : ℝ) (Ω : ℝ → ℂ) : ℂ :=
  (((2 * π / lam) / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) / cos ((θ - θ0) / 2)) ^ 2 : ℝ) : ℂ) *
    ∫ v in (-(L / 2))..(L / 2),
      Complex.exp ((((2 * π / lam) * (sin θ - sin θ0) * v : ℝ) : ℂ) * Complex.I) * Ω v

/-- Sec. III, Eq. (17c), PDF p. 8: the centred symmetric Lévy stable density of index `α`
(`0 < α ≤ 2`), `𝓛_α(x) = (1/2π) ∫_{-∞}^{∞} e^{ikx} e^{-|k|^α} dk`. The integral is real (its
imaginary part vanishes because `e^{-|k|^α}` is even), so its real part is taken. -/
def levyDensity (α x : ℝ) : ℝ :=
  (∫ k : ℝ, Complex.exp (((k * x : ℝ) : ℂ) * Complex.I) * ((Real.exp (-(|k| ^ α)) : ℝ) : ℂ)).re /
    (2 * π)

/-- Sec. III, Eq. (17b), PDF p. 8: `a = 2π√2 cos((θ+θ₀)/2) cos((θ-θ₀)/2)`. -/
def levyA (θ θ0 : ℝ) : ℝ := 2 * π * √2 * cos ((θ + θ0) / 2) * cos ((θ - θ0) / 2)

/-- Sec. III, Eq. (17a), PDF p. 8: the prefactor of the Lévy density,
`s(λ)^(-1/H) a^(-(1/H-1)) / (√2 cos θ₀) · cos((θ+θ₀)/2) / cos³((θ-θ₀)/2)`, with `s = s(λ)`. -/
def levyPrefactor (H s θ θ0 : ℝ) : ℝ :=
  s ^ (-(1 / H)) * levyA θ θ0 ^ (-(1 / H - 1)) / (√2 * cos θ0) *
    (cos ((θ + θ0) / 2) / cos ((θ - θ0) / 2) ^ 3)

/-- Sec. III, Eq. (17a), PDF p. 8: the argument of the Lévy density,
`√2 tan((θ-θ₀)/2) / (a^(1/H-1) s(λ)^(1/H))`. -/
def levyArg (H s θ θ0 : ℝ) : ℝ :=
  √2 * tan ((θ - θ0) / 2) / (levyA θ θ0 ^ (1 / H - 1) * s ^ (1 / H))

/-- Sec. III, Eqs. (17a)-(17c), PDF p. 8: the closed form of the mean differential reflection
coefficient of a perfectly conducting Gaussian self-affine surface (Hurst exponent `H`, slope
`s = s(λ)` over one wavelength) in the Kirchhoff approximation,
`⟨∂R_s/∂θ⟩ = levyPrefactor · 𝓛_{2H}(levyArg)`. -/
def mdrcFinal (H s θ θ0 : ℝ) : ℝ :=
  levyPrefactor H s θ θ0 * levyDensity (2 * H) (levyArg H s θ θ0)

/-- Sec. IV, PDF p. 13: the horizontal distance over which the angular retardation
`(sin θ - sin θ₀) Δx` equals the wavelength, `δ_ang = λ / (sin θ - sin θ₀)`. -/
def deltaAng (lam θ θ0 : ℝ) : ℝ := lam / (sin θ - sin θ0)

/-- Sec. IV, PDF p. 13: the horizontal distance over which the roughness retardation
`(cos θ + cos θ₀) Δz`, with `Δz = σ(Δx)` of Eq. (4), equals the wavelength,
`δ_rough = λ s(λ)^(-1/H) / (cos θ + cos θ₀)^(1/H)`. -/
def deltaRough (lam H s θ θ0 : ℝ) : ℝ :=
  lam * s ^ (-(1 / H)) / (cos θ + cos θ0) ^ (1 / H)

/-- Sec. IV, PDF p. 13: the ratio `χ = δ_rough / δ_ang
= (sin θ - sin θ₀) s(λ)^(-1/H) / (cos θ + cos θ₀)^(1/H)`. -/
def chiRatio (lam H s θ θ0 : ℝ) : ℝ := deltaRough lam H s θ θ0 / deltaAng lam θ θ0

end Arxivcond_mat_0408414


