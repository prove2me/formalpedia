-- Prove2me | Definitions.Def_SchrodingerEquation_infinite_well_model
-- name    : SchrodingerEquation_infinite_well_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T18:18:46.875815+00:00
-- url     : https://prove2.me/theorems/5af5c48e-496e-4a9c-8580-36e6ce5edc09
-- title:
--   Model of the one-dimensional infinite potential well
-- statement:
--   This file fixes the model for a particle of mass $m$ in a one-dimensional **infinite potential well** of width $L > 0$, with reduced Planck constant $\hbar$.
--
--   **Stationary states.** For real parameters $\hbar, m, L, E$ and a function $\psi : \mathbb{R} \to \mathbb{C}$, the predicate `IsStationaryState` holds when all of the following are true:
--
--   - $\psi$ is continuous on the closed interval $[0, L]$;
--   - $\psi$ is differentiable at every point of the open interval $(0, L)$, and its derivative $\psi'$ is again differentiable at every point of $(0, L)$;
--   - the time-independent Schrödinger equation with vanishing potential holds inside the box,
--     $$-\frac{\hbar^{2}}{2m}\,\psi''(x) = E\,\psi(x) \qquad (0 < x < L),$$
--     where the real coefficient is coerced into $\mathbb{C}$;
--   - the wave function vanishes at the two walls: $\psi(0) = 0$ and $\psi(L) = 0$.
--
--   Nothing is required of $\psi$ outside $[0, L]$: the infinite walls make the wave function vanish there, and no statement in this mission refers to those values.
--
--   **Energy levels.** `energyLevel` is the real number
--   $$E_n = \frac{n^{2}\pi^{2}\hbar^{2}}{2 m L^{2}}, \qquad n \in \mathbb{N},$$
--   defined for all natural $n$ (including $n = 0$, where it equals $0$).
--
--   **Eigenfunctions.** `eigenfunction` is the unnormalized standing wave
--   $$\psi_n(x) = \sin\!\left(\frac{n \pi x}{L}\right),$$
--   regarded as a complex-valued function of the real variable $x$.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Mathlib

namespace SchrodingerEquation

/-- `IsStationaryState hbar m L E psi` says that the complex-valued function `psi` is a
stationary state of energy `E` for a particle of mass `m` in the one-dimensional infinite
potential well of width `L`: inside the box the potential vanishes, so `psi` solves the
time-independent Schrödinger equation `-(hbar^2 / (2 * m)) * psi'' = E * psi` on the open
interval `(0, L)`; `psi` is continuous up to the walls and vanishes at both walls. -/
def IsStationaryState (hbar m L E : ℝ) (psi : ℝ → ℂ) : Prop :=
  ContinuousOn psi (Set.Icc 0 L) ∧
    (∀ x ∈ Set.Ioo 0 L, DifferentiableAt ℝ psi x) ∧
    (∀ x ∈ Set.Ioo 0 L, DifferentiableAt ℝ (deriv psi) x) ∧
    (∀ x ∈ Set.Ioo 0 L,
      ((-(hbar ^ 2 / (2 * m)) : ℝ) : ℂ) * deriv (deriv psi) x = (E : ℂ) * psi x) ∧
    psi 0 = 0 ∧ psi L = 0

/-- The `n`-th energy level of the one-dimensional infinite potential well of width `L`:
`energyLevel hbar m L n = n ^ 2 * π ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)`. -/
noncomputable def energyLevel (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The unnormalized `n`-th eigenfunction of the one-dimensional infinite potential well of
width `L`: `x ↦ sin (n * π * x / L)`, regarded as a complex-valued function of a real
variable. -/
noncomputable def eigenfunction (L : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun x => (Real.sin ((n : ℝ) * Real.pi * x / L) : ℂ)

end SchrodingerEquation


