-- Prove2me | Definitions.Def_Arxiv2009_12420_Basic
-- name    : Arxiv2009_12420_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T09:13:38.715301+00:00
-- url     : https://prove2.me/theorems/92b6bc6c-ffac-4b11-919e-f701950fa5a6
-- title:
--   Fluid media, 1D Kirchhoff integral, Helmholtz Green's function and layer potentials of a layered rough seafloor
-- statement:
--   Objects of Sections II-IV of Olson and Jackson (2020), for 2D scattering (1D roughness) from a water half-space $\Omega_0$ over a fluid layer $\Omega_1$ over a fluid basement $\Omega_2$.
--
--   1. **Media (Section II).** Each domain $\Omega_n$ has a phase speed $c_n>0$, a density $\rho_n>0$ and a loss parameter $\delta_n\ge0$. Its complex sound speed is $\tilde c_n=c_n/(1+i\delta_n)$ (eq. 1), its wavenumber at angular frequency $\omega$ is $k_n=\omega/\tilde c_n$, and the density ratios are $a_{\rho n}=\rho_n/\rho_0$.
--   2. **Roughness correlation (eq. 8).** A normalized correlation function $C_n$ of a stationary interface satisfies $C_n(0)=1$, $C_n(-x)=C_n(x)$ and $|C_n(x)|\le1$.
--   3. **1D Kirchhoff integral (eq. 23).** For the water wavenumber $k_0>0$, the rms height $h_n$, the horizontal wavenumber difference $\Delta K_x=k_{sx}-k_{ix}$ and an argument $\eta\in\mathbb{C}$,
--   $$I_n^{1D}(\eta)=2e^{-\eta^2h_n^2}\int_0^\infty\cos\Big(\frac{\Delta K_x u}{k_0}\Big)\Big[e^{\eta^2h_n^2C_n(u/k_0)}-1\Big]\,du .$$
--   4. **Green's function (eqs. 26-27).** $G_n(\mathbf r,\mathbf r_0)=\tfrac{i}{4}H_0^{(1)}(k_n|\mathbf r-\mathbf r_0|)$, the solution of $\nabla^2G_n+k_n^2G_n=-\delta$, where $H_0^{(1)}=J_0+iY_0$ and $J_0$, $Y_0$ are given by their power series (DLMF 10.2.2, 10.8.2) with the principal logarithm.
--   5. **Interfaces (Section II, Fig. 1).** $\Gamma_1$ and $\Gamma_2$ are graphs $z=g_1(x)$ and $z=g_2(x)$; a function on an interface is written as a function of the abscissa $x$. The arc-length element is $dS=\sqrt{1+g'(t)^2}\,dt$. Both unit normals point into $\Omega_1$: $\hat n_1=(g_1',-1)/\sqrt{1+g_1'^2}$ (down) on $\Gamma_1$ and $\hat n_2=(-g_2',1)/\sqrt{1+g_2'^2}$ (up) on $\Gamma_2$.
--   6. **Layer potentials (eqs. 29-30).** For media $n$ and interfaces $\Gamma_l,\Gamma_m$,
--   $$\mathbb V^n_{l,m}[\varphi](\mathbf r_l)=\int_{\Gamma_m}G_n(\mathbf r_l,\mathbf r_m)\varphi(\mathbf r_m)\,dS_m,\qquad \mathbb K^n_{l,m}[\varphi](\mathbf r_l)=\int_{\Gamma_m}\frac{\partial G_n(\mathbf r_l,\mathbf r_m)}{\partial n_m}\varphi(\mathbf r_m)\,dS_m,$$
--   with $\partial/\partial n_m=\hat n_m\cdot\nabla_{\mathbf r_m}$.
--   7. **Corner fraction (text after eq. 30).** $\alpha=\beta/(2\pi)$, where $\beta$ is the angle subtended by the one-sided tangent lines at the point. For the domain above $z=g(x)$, $\beta=\pi+\arctan g'(x^-)-\arctan g'(x^+)$; for the domain below it is $2\pi$ minus this. At smooth points $\alpha=1/2$.
--
--   **Formalization Note** Mathlib has no Hankel functions, so $J_0$ and $Y_0$ are defined by their power series. Integrals over an interface are Lebesgue integrals over the abscissa. Derivatives of the interface height and of the Green's function are Mathlib's `deriv`, and one-sided slopes are `derivWithin` on half-lines. The correlation function is described by the three properties listed in item 2, not built from a random process. The paper prints $G_n=-\tfrac i4H_0^{(1)}$ with $+\delta$ on the right of eq. (26). With that sign, Green's second identity gives every $\mathbb V$ and $\mathbb K$ term of its integral equations (28), (31), (32) with the opposite sign. Those equations, and so eq. (33), are correct for $G_n=+\tfrac i4H_0^{(1)}$, which is the sign used here.
-- source:
--   Olson and Jackson, Scattering from layered seafloors: Comparisons between theory and integral equations, arXiv:2009.12420v1 (2020), Section II (eqs. (1), (8)), Section III (eq. (23)), Section IV (eqs. (26)-(30) and text after eq. (30))

import Mathlib

/-!
Olson and Jackson, *Scattering from layered seafloors: Comparisons between theory and integral
equations*, arXiv:2009.12420v1 (2020): the fluid media and wavenumbers of Section II, the
normalized roughness correlation function (eqs. (8)-(9)), the one-dimensional Kirchhoff integral
of eq. (23) (Section III), and the Green's function, interface geometry and single- and
double-layer potential operators of the integral equations of Section IV (eqs. (26)-(33)).
-/

noncomputable section

namespace Arxiv2009_12420

open Complex MeasureTheory

/-! ### Section II: media and roughness -/

/-- Section II, first paragraphs: a fluid domain `Ω_n` is characterized by a phase speed `c_n`,
a density `ρ_n` and a dimensionless loss parameter `δ_n`. -/
structure Medium where
  /-- phase speed `c_n` (m/s) -/
  c : ℝ
  /-- density `ρ_n` (kg/m³) -/
  rho : ℝ
  /-- loss parameter `δ_n` -/
  delta : ℝ

/-- Section II: the physical standing assumptions on a fluid medium, `c_n > 0`, `ρ_n > 0` and
`δ_n ≥ 0`. -/
def Medium.IsPhysical (m : Medium) : Prop :=
  0 < m.c ∧ 0 < m.rho ∧ 0 ≤ m.delta

/-- Section II, eq. (1): the complex sound speed `c̃_n = c_n / (1 + i δ_n)`. -/
def Medium.complexSpeed (m : Medium) : ℂ :=
  (m.c : ℂ) / (1 + I * (m.delta : ℂ))

/-- Section II, text after eq. (1): the wavenumber `k_n = ω / c̃_n` at angular frequency `ω`. -/
def Medium.wavenumber (m : Medium) (ω : ℝ) : ℂ :=
  (ω : ℂ) / m.complexSpeed

/-- Section II, text after eq. (1): the density ratio `a_{ρn} = ρ_n / ρ_0`. -/
def densityRatio (m m0 : Medium) : ℝ :=
  m.rho / m0.rho

/-- Section II, eq. (8): the normalized correlation function `C_n(x) = h_n^{-2} ⟨f_n(x') f_n(x + x')⟩`
of a stationary rough interface, recorded through the properties this normalization and
stationarity give it: `C_n(0) = 1`, `C_n(-x) = C_n(x)` and `|C_n(x)| ≤ 1`. -/
def IsNormalizedCorrelation (C : ℝ → ℝ) : Prop :=
  C 0 = 1 ∧ (∀ x, C (-x) = C x) ∧ ∀ x, |C x| ≤ 1

/-! ### Section III: the one-dimensional Kirchhoff integral -/

/-- Section III, eq. (23): the 1D Kirchhoff integral
`I_n^{1D}(η) = 2 e^{-η² h_n²} ∫_0^∞ cos(ΔK_x u / k_0) [e^{η² h_n² C_n(u/k_0)} - 1] du`,
with `k_0` the water wavenumber, `h_n` the rms height and `C_n` the normalized correlation
function of interface `n`, and `ΔK_x = k_{sx} - k_{ix}`. -/
def kirchhoffIntegral1D (k0 h dKx : ℝ) (C : ℝ → ℝ) (η : ℂ) : ℂ :=
  2 * cexp (-(η ^ 2 * (h : ℂ) ^ 2)) *
    ∫ u in Set.Ioi (0 : ℝ),
      (Real.cos (dKx * u / k0) : ℂ) * (cexp (η ^ 2 * (h : ℂ) ^ 2 * (C (u / k0) : ℂ)) - 1)

/-! ### Section IV: Green's function and layer potentials -/

/-- Eq. (27): the Bessel function `J₀(z) = ∑_{m ≥ 0} (-1)^m (z/2)^{2m} / (m!)²` (DLMF 10.2.2). -/
def besselJ0 (z : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * (z / 2) ^ (2 * m) / ((m.factorial : ℂ) ^ 2)

/-- Eq. (27): the Bessel function of the second kind
`Y₀(z) = (2/π)(log(z/2) + γ) J₀(z) + (2/π) ∑_{m ≥ 1} (-1)^{m+1} H_m (z/2)^{2m} / (m!)²`, with `H_m`
the harmonic numbers, `γ` Euler's constant and the principal logarithm (DLMF 10.8.2); the `m = 0`
term of the sum vanishes since `H_0 = 0`. -/
def besselY0 (z : ℂ) : ℂ :=
  (2 / (Real.pi : ℂ)) * ((Complex.log (z / 2) + (Real.eulerMascheroniConstant : ℂ)) * besselJ0 z) +
    (2 / (Real.pi : ℂ)) *
      ∑' m : ℕ, (-1 : ℂ) ^ (m + 1) * (harmonic m : ℂ) * (z / 2) ^ (2 * m) / ((m.factorial : ℂ) ^ 2)

/-- Eq. (27): the Hankel function of the first kind and order zero, `H₀^{(1)} = J₀ + i Y₀`. -/
def hankel0 (z : ℂ) : ℂ :=
  besselJ0 z + I * besselY0 z

/-- Eqs. (26)-(27): the 2D free-space Green's function of a medium with wavenumber `k`,
`G(r, r₀) = (i/4) H₀^{(1)}(k |r - r₀|)`, the solution of `∇²G + k²G = -δ`, for points
`r = (r_x, r_z)`, `r₀ = (r_{x0}, r_{z0})`. The paper prints `(-i/4) H₀^{(1)}` with `+δ`; with that
sign every `𝕍` and `𝕂` term of its integral equations (28), (31), (32) has the wrong sign, and those
equations (hence eq. (33)) hold for the opposite sign used here. -/
def green (k : ℂ) (r r0 : ℝ × ℝ) : ℂ :=
  I / 4 * hankel0 (k * (Real.sqrt ((r.1 - r0.1) ^ 2 + (r.2 - r0.2) ^ 2) : ℂ))

/-- Section II and Fig. 1: the point `(x, g(x))` of an interface given as the graph of its height
function `g` (`Γ_n` is specified by `f_n(x)`). -/
def pt (g : ℝ → ℝ) (x : ℝ) : ℝ × ℝ :=
  (x, g x)

/-- Eqs. (29)-(30): the arc-length factor `dS = √(1 + g'(t)²) dt` of an interface `z = g(x)`. -/
def arcFactor (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (1 + deriv g t ^ 2)

/-- Section II and Fig. 1: the unit normal `n̂_1` of the upper interface `Γ_1 : z = g(x)`, which
points down into the layer `Ω_1`: `(g'(t), -1) / √(1 + g'(t)²)`. -/
def normalTop (g : ℝ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (deriv g t / arcFactor g t, -1 / arcFactor g t)

/-- Section II and Fig. 1: the unit normal `n̂_2` of the lower interface `Γ_2 : z = g(x)`, which
points up into the layer `Ω_1`: `(-g'(t), 1) / √(1 + g'(t)²)`. -/
def normalBottom (g : ℝ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (-deriv g t / arcFactor g t, 1 / arcFactor g t)

/-- Eq. (30): the normal derivative `∂G(r, r_m)/∂n_m = n̂_m · ∇_{r_m} G(r, r_m)` of a kernel in its
second argument, at the point `r_m` along the unit vector `n`. -/
def normalDerivSecond (G : ℝ × ℝ → ℝ × ℝ → ℂ) (r : ℝ × ℝ) (n r0 : ℝ × ℝ) : ℂ :=
  (n.1 : ℂ) * deriv (fun s : ℝ => G r (s, r0.2)) r0.1 +
    (n.2 : ℂ) * deriv (fun s : ℝ => G r (r0.1, s)) r0.2

/-- Eq. (29): the single-layer potential operator `𝕍^n_{l,m}` of a medium with wavenumber `k`,
`𝕍^n_{l,m}[φ](r_l) = ∫_{Γ_m} G_n(r_l, r_m) φ(r_m) dS_m`, with `Γ_l : z = g_l(x)` and
`Γ_m : z = g_m(x)`; functions on an interface are written as functions of the abscissa. -/
def singleLayer (k : ℂ) (gl gm : ℝ → ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, green k (pt gl x) (pt gm t) * φ t * (arcFactor gm t : ℂ)

/-- Eq. (30): the double-layer potential operator `𝕂^n_{l,m}` of a medium with wavenumber `k`,
`𝕂^n_{l,m}[φ](r_l) = ∫_{Γ_m} ∂G_n(r_l, r_m)/∂n_m φ(r_m) dS_m`, where `nm` is the unit normal of
`Γ_m` (`normalTop` for `Γ_1`, `normalBottom` for `Γ_2`; both point into `Ω_1`). -/
def doubleLayer (k : ℂ) (gl gm : ℝ → ℝ) (nm : ℝ → ℝ × ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, normalDerivSecond (green k) (pt gl x) (nm t) (pt gm t) * φ t * (arcFactor gm t : ℂ)

/-- Text after eq. (30): `α = β / (2π)` at a point of the interface `z = g(x)`, where `β` is the
angle subtended above the interface by its one-sided tangent lines at `(x, g(x))`:
`β = π + arctan g'(x⁻) - arctan g'(x⁺)`; `α = 1/2` at smooth points. This is the fraction for the
domain lying above the interface (`Ω_0` for `Γ_1`). -/
def alphaAbove (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.pi + Real.arctan (derivWithin g (Set.Iic x) x) - Real.arctan (derivWithin g (Set.Ici x) x)) /
    (2 * Real.pi)

/-- Text after eq. (30): `α = β / (2π)` for the domain lying below the interface `z = g(x)`
(`Ω_2` for `Γ_2`): `1 - alphaAbove g x`. -/
def alphaBelow (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 - alphaAbove g x

end Arxiv2009_12420


