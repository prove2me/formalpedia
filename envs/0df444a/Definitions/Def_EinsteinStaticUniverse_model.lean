-- Prove2me | Definitions.Def_EinsteinStaticUniverse_model
-- name    : EinsteinStaticUniverse_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T04:16:41.942169+00:00
-- url     : https://prove2.me/theorems/27f746c1-28cb-4161-966a-470440315b43
-- title:
--   Friedmann model for dust with a cosmological constant
-- statement:
--   This file fixes the kinematic and dynamical model used by every statement of the mission: a spatially homogeneous, isotropic universe filled with pressureless matter ("dust") and a cosmological constant $\Lambda$, in geometrized units with $c=1$.
--
--   A universe is described by a **scale factor** $a$, a real function of cosmic time. Dust dilutes with volume, so its energy density at scale factor $x$ is
--   $$\rho(x)=\rho_0\left(\frac{a_0}{x}\right)^{3},$$
--   with reference constants $\rho_0$ (a density) and $a_0$ (a scale factor). A cosmological constant is equivalently described as a **vacuum fluid** of constant density $\rho_{\text{vac}}=\Lambda/(8\pi G)$ and pressure $p_{\text{vac}}=-\rho_{\text{vac}}$, that is, equation of state $w=-1$.
--
--   The dynamics are the two Friedmann equations. For a fluid of density $\rho(t)$, curvature constant $k$ and cosmological constant $\Lambda$, the **first Friedmann equation** on a set of times $I$ is
--   $$\dot a(t)^{2}=\frac{8\pi G}{3}\rho(t)a(t)^{2}-k+\frac{\Lambda}{3}a(t)^{2},\qquad t\in I,$$
--   and the **acceleration equation** for dust is
--   $$\ddot a(t)=F\big(a(t)\big),\qquad F(x)=-\frac{4\pi G}{3}\rho(x)\,x+\frac{\Lambda}{3}x .$$
--   The file also defines the **continuity equation** $\dot\rho+3(\dot a/a)(\rho+p)=0$, the **Hubble parameter** $H=\dot a/a$, the **critical density** $\rho_c=3H^2/(8\pi G)$, and the three density parameters
--   $$\Omega_m=\frac{\rho}{\rho_c},\qquad \Omega_\Lambda=\frac{\Lambda}{3H^{2}},\qquad \Omega_k=-\frac{k}{a^{2}H^{2}} .$$
--
--   These definitions are the common vocabulary of the mission: the Einstein static universe, its instability, the vacuum-energy reading of $\Lambda$ and the density-parameter identity are all phrased in terms of them, so that every statement commits to the same sign conventions and to the same meaning of "solution".
--
--   **Formalization Note.** Each equation is a predicate on a scale factor and an explicit set of times, so a statement can require it on all of $\mathbb{R}$, on $[0,\infty)$, on a bounded interval, or on a general open set. The acceleration function $F$ is separated out as a function of the scale factor alone, which is what makes the equilibrium analysis possible.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib

namespace EinsteinStaticUniverse

open Real

/-- Energy density of pressureless matter ("dust") at scale factor `a`, normalised by the
reference values `ρ₀` (density) and `a₀` (scale factor): `ρ(a) = ρ₀ (a₀ / a)³`. -/
noncomputable def dustDensity (ρ₀ a₀ a : ℝ) : ℝ := ρ₀ * (a₀ / a) ^ 3

/-- The vacuum energy density equivalent to a cosmological constant `Λ`,
`ρ_vac = Λ / (8πG)`, i.e. `Λ = κ ρ_vac` with `κ = 8πG` in units with `c = 1`. -/
noncomputable def vacuumDensity (G Λ : ℝ) : ℝ := Λ / (8 * π * G)

/-- The pressure of the vacuum fluid equivalent to a cosmological constant `Λ`:
`p_vac = -ρ_vac`, i.e. equation of state `w = -1`. -/
noncomputable def vacuumPressure (G Λ : ℝ) : ℝ := -(Λ / (8 * π * G))

/-- The first Friedmann equation for a homogeneous isotropic universe filled with a fluid of
energy density `ρ t`, with curvature constant `k` and cosmological constant `Λ`:
`(ȧ)² = (8πG/3) ρ a² - k + (Λ/3) a²`, required at every time of the set `I`. -/
def FriedmannGeneral (G Λ k : ℝ) (ρ : ℝ → ℝ) (a : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, (deriv a t) ^ 2 = (8 * π * G / 3) * ρ t * (a t) ^ 2 - k + (Λ / 3) * (a t) ^ 2

/-- The first Friedmann equation for a dust-filled universe with curvature constant `k` and
cosmological constant `Λ`. -/
def FriedmannI (G Λ k ρ₀ a₀ : ℝ) (a : ℝ → ℝ) (I : Set ℝ) : Prop :=
  FriedmannGeneral G Λ k (fun t => dustDensity ρ₀ a₀ (a t)) a I

/-- The right-hand side of the acceleration equation for dust, as a function of the scale
factor: `F(x) = -(4πG/3) ρ(x) x + (Λ/3) x = -(4πG/3) ρ₀ a₀³ / x² + (Λ/3) x`. -/
noncomputable def accel (G Λ ρ₀ a₀ : ℝ) (x : ℝ) : ℝ :=
  -(4 * π * G / 3) * dustDensity ρ₀ a₀ x * x + (Λ / 3) * x

/-- The second (acceleration) Friedmann equation for pressureless matter with cosmological
constant `Λ`: `ä = -(4πG/3) ρ a + (Λ/3) a`, required at every time of the set `I`. -/
def FriedmannII (G Λ ρ₀ a₀ : ℝ) (a : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, deriv (deriv a) t = accel G Λ ρ₀ a₀ (a t)

/-- The continuity (energy conservation) equation for a fluid of energy density `ρ` and
pressure `p` in a universe with scale factor `a`: `ρ̇ + 3 (ȧ/a) (ρ + p) = 0` on `I`. -/
def ContinuityEquation (ρ p : ℝ → ℝ) (a : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, deriv ρ t + 3 * (deriv a t / a t) * (ρ t + p t) = 0

/-- The Hubble parameter `H = ȧ / a`. -/
noncomputable def hubbleParameter (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- The critical density `ρ_c = 3H² / (8πG)`. -/
noncomputable def criticalDensity (G H : ℝ) : ℝ := 3 * H ^ 2 / (8 * π * G)

/-- The matter density parameter `Ω_m = ρ / ρ_c`. -/
noncomputable def omegaM (G H ρ : ℝ) : ℝ := ρ / criticalDensity G H

/-- The dark-energy density parameter `Ω_Λ = Λ / (3H²)`. -/
noncomputable def omegaLambda (Λ H : ℝ) : ℝ := Λ / (3 * H ^ 2)

/-- The curvature density parameter `Ω_k = -k / (a²H²)`. -/
noncomputable def omegaK (k a H : ℝ) : ℝ := -k / (a ^ 2 * H ^ 2)

end EinsteinStaticUniverse


