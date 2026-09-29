-- Prove2me | Definitions.Def_FriedmannEquations_Defs
-- name    : FriedmannEquations_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T21:17:32.090834+00:00
-- url     : https://prove2.me/theorems/7b7fa273-8462-4853-9e73-6e424e287203
-- title:
--   Friedmann equations: Hubble parameter, the two Friedmann equations, fluid equation, critical density, density parameter
-- statement:
--   Basic objects of Friedmann–Lemaître–Robertson–Walker cosmology, in units with $c = 1$. A scale factor $R(t)$, an energy density $\rho(t)$ and an isotropic pressure $p(t)$ are real functions of time; $G$ is Newton's constant, $\Lambda$ the cosmological constant and $k$ the spatial-curvature constant.
--
--   * **Hubble parameter:** $H(t) = \dot R(t)/R(t)$.
--   * **First Friedmann equation** at time $t$:
--   $$H^2 = \Big(\frac{\dot R}{R}\Big)^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2} + \frac{\Lambda}{3}.$$
--   * **Second Friedmann equation** at time $t$:
--   $$\frac{\ddot R}{R} = \frac{\Lambda}{3} - \frac{4\pi G}{3}(\rho + 3p).$$
--   * **Fluid (continuity) equation** at time $t$: $\dot\rho = -3H(\rho + p)$.
--   * **Critical density** of a Hubble rate $H$: $\rho_c = \dfrac{3H^2}{8\pi G}$.
--   * **Density parameter:** $\Omega = \rho/\rho_c = \dfrac{8\pi G\rho}{3H^2}$.
--
--   Derivatives are Mathlib's `deriv`; the equations are pointwise predicates, so solutions on a time interval are expressed by quantifying over the interval.
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), sections "Equations" (p. 2), "Spatial curvature"/"Critical density" (pp. 2–3), "Density parameter" (pp. 3–4).

import Mathlib

namespace FriedmannEquations

/-- The Hubble parameter `H(t) = Ṙ(t) / R(t)` of a scale factor `R`. -/
noncomputable def hubble (R : ℝ → ℝ) (t : ℝ) : ℝ := deriv R t / R t

/-- The first Friedmann equation at time `t` (units with `c = 1`):
`(Ṙ/R)² = 8πGρ/3 − k/R² + Λ/3`. -/
def FirstFriedmannEq (G Λ k : ℝ) (R ρ : ℝ → ℝ) (t : ℝ) : Prop :=
  hubble R t ^ 2 = 8 * Real.pi * G * ρ t / 3 - k / R t ^ 2 + Λ / 3

/-- The second Friedmann (acceleration) equation at time `t` (units with `c = 1`):
`R̈/R = Λ/3 − (4πG/3)(ρ + 3p)`. -/
def SecondFriedmannEq (G Λ : ℝ) (R ρ p : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (deriv R) t / R t = Λ / 3 - 4 * Real.pi * G / 3 * (ρ t + 3 * p t)

/-- The fluid (continuity) equation at time `t` (units with `c = 1`):
`ρ̇ = −3H(ρ + p)`. -/
def FluidEq (R ρ p : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv ρ t = -3 * hubble R t * (ρ t + p t)

/-- The critical density `ρ_c = 3H² / (8πG)`. -/
noncomputable def criticalDensity (G H : ℝ) : ℝ := 3 * H ^ 2 / (8 * Real.pi * G)

/-- The density parameter `Ω = ρ / ρ_c = 8πGρ / (3H²)`. -/
noncomputable def densityParameter (G H ρ : ℝ) : ℝ := ρ / criticalDensity G H

end FriedmannEquations


