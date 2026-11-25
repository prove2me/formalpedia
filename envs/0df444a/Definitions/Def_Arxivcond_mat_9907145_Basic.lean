-- Prove2me | Definitions.Def_Arxivcond_mat_9907145_Basic
-- name    : Arxivcond_mat_9907145_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:29:25.561883+00:00
-- url     : https://prove2.me/theorems/459df6ae-4e1b-50f6-9488-32ed0be348c9
-- title:
--   Kirchhoff amplitude and mean differential reflection coefficient of a random profile, increment characteristic function, Gaussian self-affine Omega, Lévy stable density, closed-form mean DRC and Huyge
-- statement:
--   Objects of Simonsen, Vandembroucq and Roux, *Wave scattering from self-affine surfaces* (arXiv:cond-mat/9907145v1). Angles are in radians, $K=\omega/c$ is the vacuum wave number, and where the wavelength appears $\omega/c=2\pi/\lambda$.
--
--   1. **Increment scale (Eq. 3).** For Hurst exponent $H$ and topothesy $\ell$, $\sigma(\Delta x)=\ell^{1-H}\Delta x^H$ for $\Delta x\ge0$.
--   2. **Kirchhoff amplitude (Eq. 9).** For a profile $z=f(x)$ on $|x|\le L/2$, with $q=K\sin\theta$, $k=K\sin\theta_0$, $\alpha_0(q)=K\cos\theta$, $\alpha_0(k)=K\cos\theta_0$, and the incident wave $\Phi_0=e^{ikx-i\alpha_0(k)z}$,
--   $$R(q|k)=\frac{-i}{2\alpha_0(q)}\int_{-L/2}^{L/2}e^{-iqx-i\alpha_0(q)f(x)}\,\mathcal N(x)\,dx,\qquad \mathcal N(x)=2\big(-f'(x)\,ik-i\alpha_0(k)\big)e^{ikx-i\alpha_0(k)f(x)},$$
--   which is $\mathcal N=2\partial_n\Phi_0|_{z=f(x)}$ with $\partial_n=-f'\partial_x+\partial_z$.
--   3. **Mean differential reflection coefficient (Eq. 8).** For a random profile $\zeta$ under a probability measure $P$, $\langle\partial R/\partial\theta\rangle_L=\frac1L\frac{K}{2\pi}\frac{\cos^2\theta}{\cos\theta_0}\,\mathbb E|R(q|k)|^2$.
--   4. **Characteristic function of the increment (Eq. 11).** $\Omega(v)=\mathbb E\exp\{-iK(\cos\theta+\cos\theta_0)(\zeta(0)-\zeta(v))\}$.
--   5. **Reduced form (Eq. 10).** For any function $\Omega$,
--   $$\mathcal K_L[\Omega]=\frac{K}{2\pi}\frac{1}{\cos\theta_0}\frac{\cos^2\frac{\theta+\theta_0}{2}}{\cos^2\frac{\theta-\theta_0}{2}}\int_{-L/2}^{L/2}e^{iK(\sin\theta-\sin\theta_0)v}\,\Omega(v)\,dv .$$
--   6. **Gaussian $\Omega$ (Eqs. 4, 12).** $\Omega_G(v)=\int_{\mathbb R}e^{-iK(\cos\theta+\cos\theta_0)z}\,dN\big(0,\sigma(|v|)^2\big)(z)$, the point mass at $0$ when $\sigma=0$.
--   7. **Lévy stable density (Eq. 14b).** $\mathcal L_\alpha(x)=\frac{1}{2\pi}\int_{\mathbb R}e^{ikx}e^{-|k|^\alpha}\,dk$ (real; its real part is taken).
--   8. **Closed form (Eq. 14a).** With $r=\ell/\lambda$ and $a=\sqrt2\,\frac\omega c\,\ell\cos\frac{\theta+\theta_0}{2}\cos\frac{\theta-\theta_0}{2}=2\sqrt2\pi r\cos\frac{\theta+\theta_0}{2}\cos\frac{\theta-\theta_0}{2}$,
--   $$\mathrm{mdrc}(H,r,\theta,\theta_0)=\frac{a^{-(1/H-1)}}{\sqrt2\cos\theta_0}\,\frac{\cos\frac{\theta+\theta_0}{2}}{\cos^3\frac{\theta-\theta_0}{2}}\,\mathcal L_{2H}\Big(\frac{\sqrt2\tan\frac{\theta-\theta_0}{2}}{a^{1/H-1}}\Big).$$
--   9. **Huygens length scales (PDF p. 3).** $d_{ang}=\lambda/\tan\frac{\theta-\theta_0}{2}$ and $d_{rough}=\lambda^{1/H}\ell^{1-1/H}$.
--
--   **Formalization Note** The closed form is a function of $r=\ell/\lambda$ (the ratio used in Fig. 2) rather than of $\ell$ and $\lambda$ separately; Eq. (14a) depends on them only through $(\omega/c)\ell=2\pi\ell/\lambda$. The paper writes $v^H$ in Eq. (12); $\Omega_G$ uses $|v|^H$, since $\Delta\zeta(v)$ is an increment over the distance $|v|$.
-- source:
--   I. Simonsen, D. Vandembroucq and S. Roux, Wave scattering from self-affine surfaces, arXiv:cond-mat/9907145v1 (1999), main text (unsectioned letter): Eqs. (3), (4), (7)-(14b), PDF pp. 2-3; dimensional argument d_ang, d_rough, PDF p. 3

import Mathlib

/-!
I. Simonsen, D. Vandembroucq and S. Roux, *Wave scattering from self-affine surfaces*,
arXiv:cond-mat/9907145v1 (letter, unsectioned): the self-affine increment scale (Eq. (3)), the
Kirchhoff scattering amplitude (Eq. (9)) and mean differential reflection coefficient (Eq. (8)) of a
random profile of length `L`, the characteristic function `Ω(v)` of the height increment
(Eq. (11)), the reduced form (10) of the mean differential reflection coefficient, the Gaussian
`Ω` (Eqs. (4), (12)), the centred symmetric Lévy stable density (Eq. (14b)), the closed form (14a),
and the Huygens length scales `d_ang`, `d_rough` of the dimensional argument (PDF pp. 3-4).

Angles are in radians. `K` is the vacuum wave number `ω/c`; where the paper uses the wavelength,
`ω/c = 2π/λ`. The closed form is written in terms of the topothesy-to-wavelength ratio `r = ℓ/λ`,
so that `√2 (ω/c) ℓ = 2√2 π r`.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace Arxivcond_mat_9907145

/-- Eq. (3), PDF p. 2: the standard deviation of the height difference of a self-affine profile of
Hurst exponent `H` and topothesy `ℓ` over a horizontal distance `Δx ≥ 0`, `σ(Δx) = ℓ^(1-H) Δx^H`. -/
def incStd (ell H dx : ℝ) : ℝ := ell ^ (1 - H) * dx ^ H

/-- Eq. (9), PDF p. 3: the Kirchhoff scattering amplitude of the profile `z = f(x)`, `|x| ≤ L/2`,
for the incident plane wave `Φ₀(x,z) = exp(ikx - iα₀(k)z)` (Eq. (7)), with `q = K sin θ`,
`k = K sin θ₀`, `α₀(q) = K cos θ`, `α₀(k) = K cos θ₀`:
`R(q|k) = (-i/(2α₀(q))) ∫_{-L/2}^{L/2} exp(-iqx - iα₀(q) f(x)) 𝒩(x) dx`, where the source function
is `𝒩(x) = 2 ∂ₙΦ₀(x, z)|_{z = f(x)}` with `∂ₙ = -f'(x) ∂ₓ + ∂_z`, i.e.
`𝒩(x) = 2 (-f'(x) · ik - iα₀(k)) exp(ikx - iα₀(k) f(x))`. -/
def kirchhoffAmp (K θ θ0 L : ℝ) (f : ℝ → ℝ) : ℂ :=
  (-Complex.I / (2 * ((K * cos θ : ℝ) : ℂ))) *
    ∫ x in (-(L / 2))..(L / 2),
      Complex.exp (-(((K * sin θ * x + K * cos θ * f x : ℝ) : ℂ)) * Complex.I) *
        (2 * (-((deriv f x : ℝ) : ℂ) * (((K * sin θ0 : ℝ) : ℂ) * Complex.I) -
            ((K * cos θ0 : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((((K * sin θ0 * x - K * cos θ0 * f x : ℝ) : ℂ)) * Complex.I))

/-- Eq. (8), PDF p. 3: the mean differential reflection coefficient of a random profile `ζ ω` of
length `L`, `⟨∂R/∂θ⟩ = (1/L) (ω/(2πc)) (cos²θ / cos θ₀) ⟨|R(q|k)|²⟩`, with `R` the Kirchhoff
amplitude of Eq. (9) and `⟨·⟩` the expectation under `P`. -/
def meanDRC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → ℝ → ℝ)
    (K θ θ0 L : ℝ) : ℝ :=
  1 / L * (K / (2 * π)) * (cos θ ^ 2 / cos θ0) * ∫ ω, ‖kirchhoffAmp K θ θ0 L (ζ ω)‖ ^ 2 ∂P

/-- Eq. (11), PDF p. 3: `Ω(v) = ⟨exp{-i (ω/c)(cos θ + cos θ₀) Δζ(v)}⟩` with
`Δζ(v) = ζ(x) - ζ(x+v)`, evaluated at `x = 0` (for a profile with stationary increments it does not
depend on `x`). -/
def incrementCF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → ℝ → ℝ)
    (K θ θ0 v : ℝ) : ℂ :=
  ∫ ω, Complex.exp (-(((K * (cos θ + cos θ0) * (ζ ω 0 - ζ ω v) : ℝ) : ℂ)) * Complex.I) ∂P

/-- Eq. (10), PDF p. 3: the reduced form of the mean differential reflection coefficient, for a
function `Ω`:
`(ω/(2πc)) (1/cos θ₀) (cos²((θ+θ₀)/2) / cos²((θ-θ₀)/2))
  ∫_{-L/2}^{L/2} exp{i (ω/c)(sin θ - sin θ₀) v} Ω(v) dv`. -/
def kirchhoffMDRC (K θ θ0 L : ℝ) (Ω : ℝ → ℂ) : ℂ :=
  ((K / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) ^ 2 / cos ((θ - θ0) / 2) ^ 2) : ℝ) : ℂ) *
    ∫ v in (-(L / 2))..(L / 2),
      Complex.exp (((K * (sin θ - sin θ0) * v : ℝ) : ℂ) * Complex.I) * Ω v

/-- Eq. (12) (first line), PDF p. 3, with the Gaussian law of Eq. (4): `Ω(v)` for a Gaussian
self-affine profile, `Ω(v) = ∫ exp{-i (ω/c)(cos θ + cos θ₀) z} p(z; |v|) dz`, where the height
increment over the distance `|v|` is centred Gaussian with standard deviation
`σ(|v|) = ℓ^(1-H) |v|^H`. The law is Mathlib's `gaussianReal 0 σ²` (the Dirac mass at `0` if
`σ = 0`). -/
def gaussOmega (K ell H θ θ0 v : ℝ) : ℂ :=
  ∫ z, Complex.exp (-(((K * (cos θ + cos θ0) * z : ℝ) : ℂ)) * Complex.I)
    ∂(gaussianReal 0 ⟨(incStd ell H |v|) ^ 2, sq_nonneg _⟩)

/-- Eq. (14b), PDF p. 3: the centred symmetric Lévy stable density of exponent `α`,
`𝓛_α(x) = (1/2π) ∫_{-∞}^{∞} e^{ikx} e^{-|k|^α} dk`. The integral is real (its imaginary part
vanishes because `e^{-|k|^α}` is even), so its real part is taken. -/
def levyDensity (α x : ℝ) : ℝ :=
  (∫ k : ℝ, Complex.exp (((k * x : ℝ) : ℂ) * Complex.I) * ((Real.exp (-(|k| ^ α)) : ℝ) : ℂ)).re /
    (2 * π)

/-- Eq. (14a), PDF p. 3: `a = √2 (ω/c) ℓ cos((θ+θ₀)/2) cos((θ-θ₀)/2)`, written with
`(ω/c) ℓ = 2π r`, `r = ℓ/λ`. -/
def levyA (r θ θ0 : ℝ) : ℝ := √2 * (2 * π * r) * cos ((θ + θ0) / 2) * cos ((θ - θ0) / 2)

/-- Eqs. (14a)-(14b), PDF p. 3: the closed form of the mean differential reflection coefficient of
a perfectly conducting Gaussian self-affine surface (Hurst exponent `H`, topothesy over wavelength
`r = ℓ/λ`) in the Kirchhoff approximation,
`a^(-(1/H-1)) / (√2 cos θ₀) · cos((θ+θ₀)/2) / cos³((θ-θ₀)/2) · 𝓛_{2H}(√2 tan((θ-θ₀)/2) / a^(1/H-1))`. -/
def mdrcFinal (H r θ θ0 : ℝ) : ℝ :=
  levyA r θ θ0 ^ (-(1 / H - 1)) / (√2 * cos θ0) * (cos ((θ + θ0) / 2) / cos ((θ - θ0) / 2) ^ 3) *
    levyDensity (2 * H) (√2 * tan ((θ - θ0) / 2) / levyA r θ θ0 ^ (1 / H - 1))

/-- PDF p. 3, dimensional argument: `d_ang = λ / p` with `p = tan((θ-θ₀)/2)` the slope of the
isophase plane. -/
def dAng (lam θ θ0 : ℝ) : ℝ := lam / tan ((θ - θ0) / 2)

/-- PDF p. 3, dimensional argument: `d_rough = λ^(1/H) ℓ^(1-1/H)`, the horizontal length over which
the self-affine height difference is of order `λ`. -/
def dRough (lam ell H : ℝ) : ℝ := lam ^ (1 / H) * ell ^ (1 - 1 / H)

end Arxivcond_mat_9907145


