-- Prove2me | Definitions.Def_NicaiseDelayWave_InternalInstab_WaveCalculus
-- name    : NicaiseDelayWave_InternalInstab_WaveCalculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T21:29:39.5441+00:00
-- url     : https://prove2.me/theorems/fa9260fb-413c-47c3-923b-6c1da1b2e2f9
-- title:
--   Time derivatives, Laplacian, normal derivative and standard energy for complex-valued u(x, t)
-- statement:
--   For a complex-valued function $u : \mathbb R^n \times \mathbb R \to \mathbb C$, $(x,t) \mapsto u(x,t)$, and a mixed domain $(\Omega, \Gamma_D, \Gamma_N)$ with outer unit normal $\nu$, this file defines:
--
--   1. the time derivatives $u_t(x,t) = \partial_t u(x,t)$ and $u_{tt}(x,t) = \partial_t^2 u(x,t)$;
--   2. the Laplacian of a function $\varphi : \mathbb R^n \to \mathbb C$, $\Delta\varphi(x) = \sum_{i=1}^n \partial_i^2 \varphi(x)$, and the spatial Laplacian $\Delta u(x,t)$ of $u(\cdot, t)$;
--   3. the normal derivative $\dfrac{\partial\varphi}{\partial\nu}(x) = \nabla\varphi(x)\cdot\nu(x)$, where the derivative is taken within $\overline\Omega$, so that only the values of $\varphi$ on $\overline\Omega$ enter;
--   4. the **standard energy** (3.7) of the wave equation,
--   $$\mathcal E(t) = \frac12 \int_\Omega \Big\{ |u_t(x,t)|^2 + |\nabla u(x,t)|^2 \Big\}\,dx, \qquad |\nabla u|^2 = \sum_{i=1}^n \Big|\frac{\partial u}{\partial x_i}\Big|^2 .$$
--
--   These are the differential operators and the energy appearing in problem (1.12)–(1.14) and in Theorem 1.4 of Nicaise and Pignotti.
--
--   **Formalization Note** Solutions are complex valued because the instability examples of §5.2 are of the form $e^{\lambda t}\varphi(x)$ with $\lambda \in \mathbb C$; for complex $u$ the squared modulus replaces the square. The squared gradient is the sum of the squared moduli of the partial derivatives (not an operator norm). Time derivatives are `deriv` in $t$, the Laplacian is the sum of the diagonal second derivatives in the coordinate directions, and the normal derivative uses `fderivWithin` on $\overline\Omega$ because solutions are only assumed $C^1$ up to the boundary.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1563, (1.12)–(1.14); p. 1570, (3.7) (standard energy)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain

namespace NicaiseDelayWave.InternalInstab

open MeasureTheory

variable {n : ℕ}

/-- Time derivative `u_t(x, t)` of a complex-valued `u : ℝⁿ → ℝ → ℂ`. -/
noncomputable def ut (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℂ :=
  deriv (fun s => u x s) t

/-- Second time derivative `u_tt(x, t)`. -/
noncomputable def utt (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℂ :=
  deriv (fun s => ut u x s) t

/-- Laplacian `Δφ(x) = ∑ᵢ ∂²φ/∂xᵢ²(x)` of a complex-valued `φ : ℝⁿ → ℂ`. -/
noncomputable def laplacian (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ i, iteratedFDeriv ℝ 2 φ x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- Spatial Laplacian `Δu(x, t)` of `u : ℝⁿ → ℝ → ℂ`, i.e. the Laplacian of `u(·, t)`. -/
noncomputable def laplacianX (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℂ :=
  laplacian (fun y => u y t) x

/-- Normal derivative `∂φ/∂ν(x) = ∇φ(x) · ν(x)` at a point of `Ω̄`, computed as a derivative
within `Ω̄` (so it only uses the values of `φ` on `Ω̄`). -/
noncomputable def normalDeriv (D : NicaiseDelayWave.Shared.MixedDomain n) (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  fderivWithin ℝ φ (closure D.Ω) x (D.ν x)

/-- The standard energy of the wave equation (Nicaise–Pignotti (3.7)) for a complex-valued `u`:
`𝓔(t) = ½ ∫_Ω {|u_t(x, t)|² + |∇u(x, t)|²} dx`, with `|∇u|² = ∑ᵢ |∂u/∂xᵢ|²`. -/
noncomputable def stdEnergy (D : NicaiseDelayWave.Shared.MixedDomain n) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in D.Ω, (‖ut u x t‖ ^ 2 +
    ∑ i, ‖fderiv ℝ (fun y => u y t) x (EuclideanSpace.single i 1)‖ ^ 2)

end NicaiseDelayWave.InternalInstab


