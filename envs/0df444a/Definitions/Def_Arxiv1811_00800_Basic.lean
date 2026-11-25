-- Prove2me | Definitions.Def_Arxiv1811_00800_Basic
-- name    : Arxiv1811_00800_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T13:27:06.034843+00:00
-- url     : https://prove2.me/theorems/1a486d79-7aba-41b4-8ca0-edffbd6a8eca
-- title:
--   Closed paths, circulation, winding number and enhancement factor of a vorticity filament
-- statement:
--   Objects of Aubry and Roux (2019), pp. 3-4. The propagation plane is identified with $\mathbb{C}$, a point $x+iy$ standing for $(x,y)\in\mathbb{R}^2$, and the vorticity filament sits at the origin.
--
--   1. **Closed paths.** A closed path is a curve $\gamma:[0,1]\to\mathbb{C}$ that is Lipschitz on $[0,1]$ and satisfies $\gamma(0)=\gamma(1)$. Lipschitz paths include the piecewise straight acoustic paths between scattering events.
--   2. **Circulation and dephasing (Eq. (2), first equality).** For a planar velocity field $v$, the circulation along $\gamma$ is $\oint_\gamma v\cdot d\ell=\int_0^1 v(\gamma(t))\cdot\gamma'(t)\,dt$, with the Euclidean dot product of $\mathbb{R}^2$. The dephasing between $\gamma$ and its counter-propagating partner, for wavelength $\lambda$ and sound speed $c$, is $\Delta\varphi=\frac{4\pi}{\lambda c}\oint_\gamma v\cdot d\ell$.
--   3. **Velocity profiles.** Solid rotation: $v=\Omega\,r\,u_\theta$, that is $v(z)=\Omega\,iz$. Vorticity filament of circulation $\Gamma$: $v=\frac{\Gamma}{2\pi r}u_\theta$, that is $v(z)=\frac{\Gamma\,iz}{2\pi|z|^2}$ for $z\neq0$.
--   4. **Vorticity.** The vorticity of a planar field $v=(v_x,v_y)$ is $\partial_xv_y-\partial_yv_x$.
--   5. **Loops and enclosed area.** The number of loops of a closed path $\gamma$ around a point $w$ not on it is the winding number $n(\gamma,w)=\frac{1}{2\pi i}\int_0^1\frac{\gamma'(t)}{\gamma(t)-w}\,dt$. The area enclosed by $\gamma$ is $A(\gamma)=\int_{\mathbb{R}^2}n(\gamma,w)\,dw$, which for a simple positively oriented path is the area of the region it bounds.
--   6. **Aharonov-Bohm parameter.** $\alpha=\Gamma/(\lambda c)$.
--   7. **Enhancement factor.** For a probability measure $P$ on an ensemble of closed paths, with dephasing $\Delta\varphi(\omega)$ for path $\omega$, the enhancement factor is the mean normalized backscattered intensity $E=\mathbb{E}_P[1+\cos\Delta\varphi]$.
--   8. **Loop-number law (Eq. (5)).** $p_n$, $n\in\mathbb{N}$, is the probability that a path of the ensemble winds $n$ times around the filament, in either direction: $p_n=P\{n(\gamma_\omega,0)=\pm n\}$. For any sequence $p$, $E_p(\alpha)=\sum_{n\in\mathbb{N}}p_n[1+\cos(4\pi n\alpha)]$.
--   9. **Poisson model (Eq. (6)).** For a mean loop number $\beta\ge0$, $E_\beta(\alpha)=1+\operatorname{Re}\exp[\beta(e^{4i\pi\alpha}-1)]$.
--
--   **Formalization Note** The first equality of Eq. (2) is a physical model of the paper (the dephasing as a circulation); it is taken as the definition of $\Delta\varphi$. The value of the filament profile at the origin, where it is singular, is set to $0$ and never used, since every statement requires the paths to avoid the origin.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), main text pp. 3-4: Eqs. (2), (4), (5), (6) and the velocity profiles of solid rotation and of the vorticity filament

import Mathlib

/-!
G. J. Aubry and P. Roux, *Topological Effects of a Vorticity Filament on the Coherent
Backscattering Cone*, arXiv:1811.00800v2 (2019): closed acoustic paths in the 2D propagation
plane, the circulation of a flow along a path, the dephasing of counter-propagating paths
(Eq. (2)), the solid-rotation and vorticity-filament velocity profiles (pp. 3-4), the number of
loops of a path around the filament (Eq. (4)), the coherent backscattering enhancement factor and
its loop-number expansion (Eq. (5)), and the Poisson model (Eq. (6)).

The propagation plane is identified with `ℂ` (`x + i y`), and the vorticity filament sits at the
origin.
-/

open MeasureTheory Complex

noncomputable section

namespace Arxiv1811_00800

/-- A closed path of the geometrical (ray) picture, p. 3-4: a curve `γ : [0,1] → ℂ` in the
propagation plane which is Lipschitz on `[0,1]` (this covers the piecewise straight acoustic
paths between scattering events) and returns to its starting point, `γ 0 = γ 1`. -/
def IsClosedPath (γ : ℝ → ℂ) : Prop :=
  (∃ K : NNReal, LipschitzOnWith K γ (Set.Icc 0 1)) ∧ γ 0 = γ 1

/-- The circulation `∮ v · dℓ` of a planar velocity field `v` (a vector `v z ∈ ℂ ≅ ℝ²` at each
point) along the path `γ`, Eq. (2), p. 3: `∫₀¹ v(γ t) · γ'(t) dt` with the Euclidean dot
product of `ℝ²`. -/
def circulation (v : ℂ → ℂ) (γ : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ((v (γ t)).re * (deriv γ t).re + (v (γ t)).im * (deriv γ t).im)

/-- The dephasing between a closed path and its counter-propagating partner in a flow `v`,
first equality of Eq. (2), p. 3: `Δφ = (4π / (λ c)) ∮ v · dℓ`, with `λ` the wavelength and `c`
the sound speed. -/
def phaseDiff (lam c : ℝ) (v : ℂ → ℂ) (γ : ℝ → ℂ) : ℝ :=
  4 * Real.pi / (lam * c) * circulation v γ

/-- The solid-rotation velocity profile `v = Ω r u_θ`, p. 3 (before Eq. (2)). At `z = r e^{iθ}`
the unit azimuthal vector is `u_θ = i z / |z|`, so `v(z) = Ω i z`. -/
def solidRotationField (Om : ℝ) : ℂ → ℂ :=
  fun z => (Om : ℂ) * I * z

/-- The vorticity-filament velocity profile `v = Γ / (2π r) u_θ`, p. 4 (before Eq. (4)), with
`Γ` the circulation and the filament at the origin: `v(z) = Γ i z / (2π |z|²)`. (The value at
`z = 0`, where the profile is singular, is `0` and is never used.) -/
def vortexField (Gam : ℝ) : ℂ → ℂ :=
  fun z => ((Gam / (2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ) * I * z

/-- The vorticity (scalar curl) `∂v_y/∂x - ∂v_x/∂y` of a planar velocity field at `z`, the
quantity the paper calls "the vorticity field" after Eq. (2), p. 3. -/
def vorticity (v : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ v z 1).im - (fderiv ℝ v z I).re

/-- The number of loops of the closed path `γ` around the point `w`, Eq. (4), p. 4: the
winding number `(1 / 2πi) ∫₀¹ γ'(t) / (γ t - w) dt`. -/
def windingNumber (γ : ℝ → ℂ) (w : ℂ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * I)⁻¹ * ∫ t in (0 : ℝ)..1, deriv γ t / (γ t - w)

/-- The (algebraic) area `A` enclosed by the closed path `γ`, Eq. (2), p. 3: the integral over
the plane of the number of loops of `γ` around each point. For a simple, positively oriented
closed path this is the area of the region it bounds. -/
def enclosedArea (γ : ℝ → ℂ) : ℝ :=
  ∫ w : ℂ, (windingNumber γ w).re

/-- The Aharonov-Bohm (vorticity) parameter `α = Γ / (λ c)`, p. 3 (after Fig. 2). -/
def abParam (Gam lam c : ℝ) : ℝ :=
  Gam / (lam * c)

/-- The enhancement factor `E` of the coherent backscattering cone, pp. 3-4 (before Eq. (5)):
the average over an ensemble `P` of closed paths of the normalized backscattered intensity
`1 + cos Δφ` of a path and its counter-propagating partner, with `dphi ω` the dephasing of
path `ω`. -/
def enhancementFactor {W : Type*} [MeasurableSpace W] (P : Measure W) (dphi : W → ℝ) : ℝ :=
  ∫ ω, (1 + Real.cos (dphi ω)) ∂P

/-- The probability distribution `p_n` of the number of loops `n ∈ ℕ` around the filament
(at the origin) of the closed paths of an ensemble `P`, Eq. (5), p. 4: the probability that the
path winds `n` times around the origin, in either direction. -/
def loopNumberLaw {W : Type*} [MeasurableSpace W] (P : Measure W) (γ : W → ℝ → ℂ) (n : ℕ) : ℝ :=
  P.real {ω | windingNumber (γ ω) 0 = (n : ℂ) ∨ windingNumber (γ ω) 0 = -(n : ℂ)}

/-- The right-hand side of Eq. (5), p. 4: `∑_{n ∈ ℕ} p_n [1 + cos(4π n α)]` for a loop-number
distribution `p`. -/
def loopEnhancement (p : ℕ → ℝ) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, p n * (1 + Real.cos (4 * Real.pi * n * alpha))

/-- The enhancement factor of the Poisson model, right-hand side of Eq. (6), p. 4:
`E(α) = 1 + Re exp[β (e^{4iπα} - 1)]`, with `β ≥ 0` the mean number of loops. -/
def poissonEnhancement (beta : NNReal) (alpha : ℝ) : ℝ :=
  1 + (Complex.exp (((beta : ℝ) : ℂ) * (Complex.exp (((4 * Real.pi * alpha : ℝ) : ℂ) * I) - 1))).re

end Arxiv1811_00800


