-- Prove2me | Definitions.Def_Feynman1948_WaveEquation
-- name    : Feynman1948_WaveEquation
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T15:19:46.640768+00:00
-- url     : https://prove2.me/theorems/a29dcfa2-7b57-4d85-a54e-7dbffb3e6a3b
-- title:
--   Feynman (1948) §6: short-time action, one-step path-integral evolution, Hamiltonian
-- statement:
--   Definitions for Section 6 ("The wave equation") of Feynman (1948), for a particle of mass $m>0$ moving in one dimension in a real potential $V$, with $\hbar>0$.
--
--   * **Normalizing factor (Eq. 28).** $A(\varepsilon) = \left(\dfrac{2\pi\hbar\varepsilon i}{m}\right)^{1/2}$, using the principal branch of the complex square root; for $\varepsilon>0$ this is $\sqrt{2\pi\hbar\varepsilon/m}\,e^{i\pi/4}$.
--   * **Short-time action (Eq. 22).** $S(x_{k+1},x_k) = \dfrac{m\varepsilon}{2}\left(\dfrac{x_{k+1}-x_k}{\varepsilon}\right)^2 - \varepsilon V(x_{k+1})$.
--   * **One-step path-integral evolution (Eqs. 18, 23).** For a wave function $\psi:\mathbb R\to\mathbb C$,
--   $$(U_\varepsilon\psi)(x) = \frac{1}{A(\varepsilon)}\int_{\mathbb R} \exp\!\Big(\frac{i}{\hbar} S(x,y)\Big)\,\psi(y)\,dy ,$$
--   the amplitude at $x$ at time $t+\varepsilon$ obtained from the amplitude $\psi(\cdot)=\psi(\cdot,t)$ at time $t$. The integral is the Lebesgue (Bochner) integral; it is set to $0$ when the integrand is not integrable.
--   * **Hamiltonian (right-hand side of Eq. 30).** $(H\psi)(x) = \dfrac{1}{2m}\Big(\dfrac{\hbar}{i}\dfrac{d}{dx}\Big)^2\psi + V\psi = -\dfrac{\hbar^2}{2m}\psi''(x) + V(x)\psi(x)$.
--   * **Regularized Gaussian moments (Eq. 26 with footnote 13).** Following footnote 13, $\hbar$ is replaced by $\hbar(1-i\delta)$ with $\delta>0$ small, which makes the oscillatory integrals of Eq. (26) absolutely convergent:
--   $$M_n(\delta) = \int_{\mathbb R} \xi^n \exp\!\Big(\frac{i m \xi^2}{2\hbar(1-i\delta)\varepsilon}\Big)\,d\xi .$$
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, pp. 374-376, Eqs. (18), (22), (23), (26), (28), (30), footnote 13

import Mathlib

/-!
# Feynman (1948), Section 6: definitions for the one-dimensional wave equation

R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics,
Rev. Mod. Phys. 20, 367 (1948), pp. 374–376, Eqs. (18), (22), (23), (26), (28), (30).
-/

namespace Feynman1948

open Complex MeasureTheory

/-- Eq. (28): the normalizing constant `A = (2πħεi/m)^{1/2}` (principal branch). -/
noncomputable def normalizingFactor (ħ m ε : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * ħ * ε * I / m) ^ (1 / 2 : ℂ)

/-- Eq. (22): the short-time action `S(x_{k+1}, x_k) = (mε/2)((x_{k+1}-x_k)/ε)^2 - ε V(x_{k+1})`
for a particle of mass `m` in the potential `V`, with `x = x_{k+1}` and `y = x_k`. -/
noncomputable def shortTimeAction (m : ℝ) (V : ℝ → ℝ) (ε x y : ℝ) : ℝ :=
  m * ε / 2 * ((x - y) / ε) ^ 2 - ε * V x

/-- Eqs. (18)/(23): one time step of length `ε` of the path-integral evolution,
`ψ(x, t+ε) = ∫ exp((i/ħ) S(x, y)) ψ(y, t) dy / A`. -/
noncomputable def stepEvolution (ħ m : ℝ) (V : ℝ → ℝ) (ε : ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (normalizingFactor ħ m ε)⁻¹ *
    ∫ y : ℝ, exp (I * (shortTimeAction m V ε x y : ℂ) / ħ) * ψ y

/-- Right-hand side of Eq. (30): `Hψ = (1/2m)(ħ/i · d/dx)^2 ψ + V ψ = -(ħ²/2m) ψ'' + V ψ`. -/
noncomputable def hamiltonian (ħ m : ℝ) (V : ℝ → ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  -((ħ : ℂ) ^ 2 / (2 * m)) * deriv (deriv ψ) x + (V x : ℂ) * ψ x

/-- Footnote 13 regularization of the Gaussian moments of Eq. (26): `ħ` is replaced by
`ħ(1 - iδ)`, giving `∫ ξⁿ exp(i m ξ² / (2 ħ (1 - iδ) ε)) dξ`. -/
noncomputable def regularizedMoment (ħ m ε δ : ℝ) (n : ℕ) : ℂ :=
  ∫ ξ : ℝ, (ξ : ℂ) ^ n * exp (I * m * (ξ : ℂ) ^ 2 / (2 * (ħ * (1 - I * δ)) * ε))

end Feynman1948


