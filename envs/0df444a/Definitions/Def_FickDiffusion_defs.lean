-- Prove2me | Definitions.Def_FickDiffusion_defs
-- name    : FickDiffusion_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:27:27.623973+00:00
-- url     : https://prove2.me/theorems/cd14b74f-eb9d-4a3e-8eb1-ffb122dfe546
-- title:
--   Diffusion kernels (1D and n-D) and the complementary error function
-- statement:
--   Three objects used throughout the mission.
--
--   1. **One-dimensional diffusion kernel.** For a diffusion coefficient $D$, position $x\in\mathbb R$ and time $t$,
--   $$\varphi_D(x,t)=\frac{1}{\sqrt{4\pi D t}}\exp\!\Big(-\frac{x^2}{4Dt}\Big).$$
--   This is the fundamental solution of Fick's second law $\partial_t\varphi=D\,\partial_x^2\varphi$ (the heat kernel with the thermal diffusivity replaced by $D$).
--
--   2. **$n$-dimensional diffusion kernel.** For $x\in\mathbb R^n$ with the Euclidean norm $\|x\|$,
--   $$\varphi^{(n)}_D(x,t)=(4\pi D t)^{-n/2}\exp\!\Big(-\frac{\|x\|^2}{4Dt}\Big).$$
--
--   3. **Complementary error function.**
--   $$\operatorname{erfc}(x)=\frac{2}{\sqrt\pi}\int_x^{\infty}e^{-s^2}\,ds .$$
--
--   These definitions are only physically meaningful for $D>0$ and $t>0$; every theorem of the mission that uses them assumes this explicitly.
--
--   **Formalization Note** Lean's square root returns $0$ on negative inputs, division by $0$ returns $0$, and the real power uses `Real.rpow`; these junk values are never reached because all theorems assume $D>0$, $t>0$. Mathlib has no error function, so `erfc` is defined here directly by the (convergent) Gaussian tail integral.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, sections "Fick's second law" (p. 4), "Example solution 1" (p. 6), "Example solution 2" (p. 7)

import Mathlib

namespace FickDiffusion

open Real

/-- The one-dimensional fundamental solution of Fick's second law
`∂φ/∂t = D ∂²φ/∂x²` (the heat kernel with diffusivity `D`):
`φ(x,t) = 1/√(4πDt) · exp(-x²/(4Dt))`. Meaningful for `D > 0`, `t > 0`. -/
noncomputable def heatKernel (D x t : ℝ) : ℝ :=
  1 / Real.sqrt (4 * π * D * t) * Real.exp (-x ^ 2 / (4 * D * t))

/-- The `n`-dimensional Gaussian diffusion kernel on `ℝⁿ` (Euclidean space):
`φ(x,t) = (4πDt)^(-n/2) · exp(-‖x‖²/(4Dt))`. Meaningful for `D > 0`, `t > 0`. -/
noncomputable def heatKernelEuclid (n : ℕ) (D : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  (4 * π * D * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * D * t))

/-- The complementary error function `erfc x = (2/√π) ∫ₓ^∞ exp(-s²) ds`. -/
noncomputable def erfc (x : ℝ) : ℝ :=
  2 / Real.sqrt π * ∫ s in Set.Ioi x, Real.exp (-s ^ 2)

end FickDiffusion


