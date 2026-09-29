-- Prove2me | Definitions.Def_ParticleInARing_model
-- name    : ParticleInARing_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T01:19:50.353281+00:00
-- url     : https://prove2.me/theorems/561cc021-007a-496f-bb43-d2f3966153b4
-- title:
--   Particle on a ring: periodicity, normalization, $\psi_n$, $E_n$ and the Schrödinger equation
-- statement:
--   The model of a free quantum particle of mass $m$ confined to a ring of radius $R$, described in the angular coordinate $\theta$.
--
--   A state is a function $\psi : \mathbb{R} \to \mathbb{C}$. The definitions are:
--
--   - $\mathrm{IsRingPeriodic}\,\psi$: the periodic boundary condition $\psi(\theta + 2\pi) = \psi(\theta)$ for every real $\theta$, expressing that $\psi$ is single-valued on the circle.
--   - $\mathrm{IsRingNormalized}\,\psi$: the normalization $\int_0^{2\pi} |\psi(\theta)|^2\, d\theta = 1$ over one period.
--   - $\psi_n(\theta) = \frac{1}{\sqrt{2\pi}} e^{i n \theta}$ for $n \in \mathbb{Z}$, the candidate eigenfunctions.
--   - $E_n = \dfrac{n^2 \hbar^2}{2 m R^2}$ for $n \in \mathbb{Z}$, the candidate energy levels.
--   - $\mathrm{SolvesSchrodinger}$: the time-independent Schrödinger equation $-\dfrac{\hbar^2}{2 m R^2}\, \psi''(\theta) = E\, \psi(\theta)$, required at every real $\theta$, obtained from $-\frac{\hbar^2}{2m}\nabla^2\psi = E\psi$ using $\nabla^2 = R^{-2}\,\partial^2/\partial\theta^2$ on the ring.
--   - $\mathrm{IsRingEigenstate}$: a stationary state of energy $E$, i.e. a twice continuously differentiable, $2\pi$-periodic solution of that equation.
--
--   The parameters $\hbar, m, R, E$ are real; the second derivative is the iterated derivative of order $2$.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib

namespace ParticleInARing

open Complex Real

/-- Periodicity with period `2π`: the wave function is single-valued on the circle. -/
def IsRingPeriodic (ψ : ℝ → ℂ) : Prop := ∀ θ : ℝ, ψ (θ + 2 * Real.pi) = ψ θ

/-- Normalization over one period: `∫₀^{2π} ‖ψ θ‖ ^ 2 dθ = 1`. -/
def IsRingNormalized (ψ : ℝ → ℂ) : Prop :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖ψ θ‖ ^ 2 = 1

/-- The candidate eigenfunctions `ψ n θ = (1 / √(2π)) * exp (n * θ * I)`, `n : ℤ`. -/
noncomputable def eigenstate (n : ℤ) : ℝ → ℂ :=
  fun θ => (1 / Real.sqrt (2 * Real.pi) : ℝ) * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)

/-- The candidate energy levels `E n = n ^ 2 * ħ ^ 2 / (2 * m * R ^ 2)`, `n : ℤ`. -/
noncomputable def energy (hbar m R : ℝ) (n : ℤ) : ℝ :=
  (n : ℝ) ^ 2 * hbar ^ 2 / (2 * m * R ^ 2)

/-- The time-independent Schrödinger equation for a free particle of mass `m`
confined to a ring of radius `R`, in the angular coordinate:
`-(ħ ^ 2 / (2 * m * R ^ 2)) * ψ'' θ = E * ψ θ` for every `θ`. -/
def SolvesSchrodinger (hbar m R E : ℝ) (ψ : ℝ → ℂ) : Prop :=
  ∀ θ : ℝ, (-(hbar ^ 2 / (2 * m * R ^ 2)) : ℝ) * iteratedDeriv 2 ψ θ = (E : ℂ) * ψ θ

/-- A stationary state of energy `E`: a twice continuously differentiable, `2π`-periodic
solution of the Schrödinger equation on the ring. -/
structure IsRingEigenstate (hbar m R E : ℝ) (ψ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 2 ψ
  periodic : IsRingPeriodic ψ
  schrodinger : SolvesSchrodinger hbar m R E ψ

end ParticleInARing


