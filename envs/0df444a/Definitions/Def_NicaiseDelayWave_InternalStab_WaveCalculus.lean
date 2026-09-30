-- Prove2me | Definitions.Def_NicaiseDelayWave_InternalStab_WaveCalculus
-- name    : NicaiseDelayWave_InternalStab_WaveCalculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T19:49:58.86381+00:00
-- url     : https://prove2.me/theorems/acf3ab5f-1412-49f9-bf8c-ad2b7596175a
-- title:
--   Time derivatives, Laplacian, normal derivative and the standard energy 𝓔(t)
-- statement:
--   For a function $u(x,t)$ of $x\in\mathbb{R}^n$ and $t\in\mathbb{R}$ on a mixed domain $(\Omega,\Gamma_D,\Gamma_N)$ this file fixes the notation of the paper:
--
--   1. $u_t(x,t)$ and $u_{tt}(x,t)$, the first and second partial derivatives in $t$;
--   2. $\Delta u(x,t)=\sum_{i=1}^n \partial^2_{x_i}u(x,t)$, the Laplacian in $x$;
--   3. $\dfrac{\partial u}{\partial\nu}(x,t)=\nabla_x u(x,t)\cdot\nu(x)$, the normal derivative;
--   4. the **standard energy** of the wave equation,
--   $$\mathcal{E}(t)=\frac12\int_\Omega\big\{u_t^2(x,t)+|\nabla u(x,t)|^2\big\}\,dx .$$
--
--   The standard energy is the quantity whose behaviour the stability results control; for the undamped wave equation it is conserved.
--
--   **Formalization Note** Derivatives are Mathlib's `deriv`/`fderiv`/`iteratedFDeriv`; they coincide with the classical derivatives for the $C^2$ functions to which they are applied in this mission.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1571, (3.7); p. 1575, (4.11)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

variable {n : ℕ}

/-- Time derivative `u_t(x, t)` of `u : ℝⁿ → ℝ → ℝ`. -/
noncomputable def ut (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  deriv (fun s => u x s) t

/-- Second time derivative `u_tt(x, t)`. -/
noncomputable def utt (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  deriv (fun s => ut u x s) t

/-- Spatial Laplacian `Δu(x, t) = ∑ᵢ ∂²u/∂xᵢ²(x, t)`. -/
noncomputable def laplacianX (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 (fun y => u y t) x
    ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- Normal derivative `∂u/∂ν(x, t) = ∇u(x, t) · ν(x)`. -/
noncomputable def normalDeriv (D : NicaiseDelayWave.Shared.MixedDomain n) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => u y t) x (D.ν x)

/-- The standard energy of the wave equation (Nicaise–Pignotti (3.7), (4.11)):
`𝓔(t) = ½ ∫_Ω {u_t²(x, t) + |∇u(x, t)|²} dx`. -/
noncomputable def stdEnergy (D : NicaiseDelayWave.Shared.MixedDomain n) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in D.Ω, (ut u x t ^ 2 + ‖gradient (fun y => u y t) x‖ ^ 2)

end NicaiseDelayWave.InternalStab


