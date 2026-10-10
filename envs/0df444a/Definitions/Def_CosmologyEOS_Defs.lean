-- Prove2me | Definitions.Def_CosmologyEOS_Defs
-- name    : CosmologyEOS_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:30:00.630978+00:00
-- url     : https://prove2.me/theorems/affe1292-3bcd-48ec-934e-0ce739ea8e5d
-- title:
--   Equation of state in FLRW cosmology: basic definitions
-- statement:
--   Shared definitions for the mission, for real-valued functions of time $t$: scale factor $a(t)$, energy density $\varepsilon(t)$, pressure $p(t)$, Newton's constant $G$, cosmological constant $\Lambda$.
--
--   1. **Equation-of-state parameter** $w = p/\varepsilon$ (`eosParameter p ε`).
--   2. **Fluid equation** at time $t$: $\dot\varepsilon(t) = -3\,\dfrac{\dot a(t)}{a(t)}\,(\varepsilon(t)+p(t))$ (`FluidEquation a ε p t`).
--   3. **Flat Friedmann equation** at time $t$: $\left(\dfrac{\dot a(t)}{a(t)}\right)^2 = \dfrac{8\pi G}{3}\varepsilon(t)$ (`FlatFriedmannEquation G a ε t`).
--   4. **Acceleration equation** at time $t$: $3\,\dfrac{\ddot a(t)}{a(t)} = \Lambda - 4\pi G(\varepsilon(t)+3p(t))$ (`AccelerationEquation G Λ a ε p t`).
--   5. **Effective energy density and pressure**: $\varepsilon' = \varepsilon + \dfrac{\Lambda}{8\pi G}$, $p' = p - \dfrac{\Lambda}{8\pi G}$.
--   6. **Scalar-field equation of state**: $w(\dot\phi, V) = \dfrac{\frac12\dot\phi^2 - V}{\frac12\dot\phi^2 + V}$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Derivatives are Mathlib's `deriv`, which returns $0$ at points of non-differentiability, so theorems assume differentiability explicitly. Divisions are total and return $0$ on a zero denominator; theorems assume nonzero denominators where it matters.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, sections: lead (w = p/ε), 'FLRW equations and the equation of state', 'Scalar modeling'

import Mathlib

/-!
# Equation of state in FLRW cosmology — shared definitions

Source: Wikipedia, "Equation of state (cosmology)", revision 1375011367.
All quantities are real-valued; time is a real variable `t`, the scale factor is `a : ℝ → ℝ`,
the energy density is `ε : ℝ → ℝ` and the pressure is `p : ℝ → ℝ` (units with `c = 1`
in the FLRW part).
-/

namespace CosmologyEOS

open Real

/-- The equation-of-state parameter `w = p / ε` of a perfect fluid with pressure `p` and
energy density `ε`. (As a total function it returns `0` when `ε = 0`; theorems that use it
assume `ε ≠ 0`.) -/
noncomputable def eosParameter (p ε : ℝ) : ℝ := p / ε

/-- The FLRW fluid (energy-conservation) equation at time `t`:
`ε̇(t) = -3 (ȧ(t)/a(t)) (ε(t) + p(t))`. -/
def FluidEquation (a ε p : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv ε t = -3 * (deriv a t / a t) * (ε t + p t)

/-- The Friedmann equation of a spatially flat FLRW universe (no cosmological constant)
at time `t`: `(ȧ(t)/a(t))² = (8πG/3) ε(t)`. -/
def FlatFriedmannEquation (G : ℝ) (a ε : ℝ → ℝ) (t : ℝ) : Prop :=
  (deriv a t / a t) ^ 2 = 8 * π * G / 3 * ε t

/-- The Friedmann acceleration equation at time `t`:
`3 ä(t)/a(t) = Λ - 4πG (ε(t) + 3 p(t))`. -/
def AccelerationEquation (G Λ : ℝ) (a ε p : ℝ → ℝ) (t : ℝ) : Prop :=
  3 * (deriv (deriv a) t / a t) = Λ - 4 * π * G * (ε t + 3 * p t)

/-- The effective energy density `ε' = ε + Λ / (8πG)`. -/
noncomputable def effectiveEnergyDensity (G Λ ε : ℝ) : ℝ := ε + Λ / (8 * π * G)

/-- The effective pressure `p' = p - Λ / (8πG)`. -/
noncomputable def effectivePressure (G Λ p : ℝ) : ℝ := p - Λ / (8 * π * G)

/-- The equation-of-state parameter of a homogeneous scalar field with time derivative
`φ̇ = phiDot` and potential energy `V`:
`w = (½ φ̇² - V) / (½ φ̇² + V)` (equal to `0` when the denominator vanishes). -/
noncomputable def scalarFieldEOS (phiDot V : ℝ) : ℝ :=
  (phiDot ^ 2 / 2 - V) / (phiDot ^ 2 / 2 + V)

end CosmologyEOS


