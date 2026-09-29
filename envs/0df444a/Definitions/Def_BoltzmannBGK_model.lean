-- Prove2me | Definitions.Def_BoltzmannBGK_model
-- name    : BoltzmannBGK_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T22:14:34.855092+00:00
-- url     : https://prove2.me/theorems/c7493027-7846-41b5-924f-e4232e82c278
-- title:
--   The Boltzmann equation with the BGK collision operator
-- statement:
--   This file fixes the kinetic model of Question 1 of the source paper: the Boltzmann equation with the BGK collision operator, together with the hydrodynamic moments it is built from. Velocities and positions range over three-dimensional Euclidean space, particles have unit mass and the Boltzmann constant is $1$.
--
--   For a distribution function $f:\mathbb R^3\to\mathbb R$ on velocity space the three moments are the mass density, the bulk velocity and the temperature,
--
--   $$\rho[f]=\int f\,\mathrm dv,\qquad u[f]=\frac1{\rho[f]}\int v\,f\,\mathrm dv,\qquad \theta[f]=\frac1{3\rho[f]}\int |v-u[f]|^2 f\,\mathrm dv .$$
--
--   The Maxwellian with parameters $(\rho,u,\theta)$ is
--
--   $$M_{\rho,u,\theta}(v)=\frac{\rho}{(2\pi\theta)^{3/2}}\exp\Big(-\frac{|v-u|^2}{2\theta}\Big),$$
--
--   the local Maxwellian of $f$ is $f^{(0)}=M_{\rho[f],u[f],\theta[f]}$, and the BGK collision operator with relaxation time $\tau$ is $C[f]=-\tfrac1\tau\,(f-f^{(0)})$. A distribution function is called admissible when it is everywhere strictly positive, integrable, and has a finite second velocity moment. Finally, a time-dependent field $f(t,x,v)$ solves the BGK equation when it is differentiable in $t$ and in $x$ and satisfies
--
--   $$\frac{\partial f}{\partial t}+v\cdot\nabla_x f = C[f],$$
--
--   where the collision operator acts on the velocity profile $f(t,x,\cdot)$ at each fixed time and position.
--
--   This is the model on which every statement of the mission rests: the conservation laws, the entropy inequality and the slab reduction are all phrased in terms of these moments and this operator.
--
--   **Formalization Note** Integrals are Bochner integrals against the Lebesgue measure on `EuclideanSpace ℝ (Fin 3)`; the bulk velocity is a vector-valued integral. Division by the density is Lean's total division, so the moments of the zero function are junk values rather than errors, which is why positivity of the density is assumed wherever it matters. The directional derivative $v\cdot\nabla_x f$ is expressed as the Fréchet derivative in $x$ evaluated at the vector $v$.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a) and equation (*).

import Mathlib

noncomputable section

open MeasureTheory Real

namespace BoltzmannBGK

/-- Velocity space (and position space): three–dimensional Euclidean space. -/
abbrev Vel := EuclideanSpace ℝ (Fin 3)

/-- Mass density of a distribution function, `ρ[f] = ∫ f dv` (particles have unit mass). -/
def density (f : Vel → ℝ) : ℝ := ∫ v, f v

/-- Bulk (mean) velocity, `u[f] = (1/ρ) ∫ v f dv`. -/
def bulkVelocity (f : Vel → ℝ) : Vel := (density f)⁻¹ • ∫ v, f v • v

/-- Temperature, `θ[f] = (1/(3ρ)) ∫ |v - u|² f dv` (unit mass, Boltzmann constant `k_B = 1`). -/
def temperature (f : Vel → ℝ) : ℝ :=
  (∫ v, ‖v - bulkVelocity f‖ ^ 2 * f v) / (3 * density f)

/-- The Maxwellian distribution with mass density `ρ`, bulk velocity `u` and temperature `θ`:
`ρ (2πθ)^(-3/2) exp (-|v - u|²/(2θ))`. -/
def maxwellian (ρ : ℝ) (u : Vel) (θ : ℝ) (v : Vel) : ℝ :=
  ρ / (2 * π * θ) ^ (3 / 2 : ℝ) * exp (-(‖v - u‖ ^ 2 / (2 * θ)))

/-- The local Maxwellian `f⁽⁰⁾` attached to `f`: the Maxwellian whose density, bulk velocity and
temperature are those of `f`. -/
def localMaxwellian (f : Vel → ℝ) : Vel → ℝ :=
  maxwellian (density f) (bulkVelocity f) (temperature f)

/-- The BGK collision operator `C[f] = -(1/τ) (f - f⁽⁰⁾)`. -/
def collision (τ : ℝ) (f : Vel → ℝ) (v : Vel) : ℝ :=
  -(1 / τ) * (f v - localMaxwellian f v)

/-- A distribution function that is everywhere positive, integrable, and has a finite second
moment in velocity. -/
structure IsKineticState (f : Vel → ℝ) : Prop where
  pos : ∀ v, 0 < f v
  integrable : Integrable f
  integrable_sq : Integrable fun v => ‖v‖ ^ 2 * f v

/-- The Boltzmann equation with the BGK collision operator,
`∂f/∂t + v · ∇ₓ f = C[f]`, for `f : time → position → velocity → ℝ` and relaxation time `τ`. -/
structure IsBGKSolution (τ : ℝ) (f : ℝ → Vel → Vel → ℝ) : Prop where
  differentiable_time : ∀ x v, Differentiable ℝ fun t => f t x v
  differentiable_space : ∀ t v, Differentiable ℝ fun x => f t x v
  equation : ∀ t x v,
    deriv (fun s => f s x v) t + fderiv ℝ (fun y => f t y v) x v = collision τ (f t x) v

end BoltzmannBGK


