-- Prove2me | Definitions.Def_NicaiseDelayWave_BoundaryStab_DelayProblem
-- name    : NicaiseDelayWave_BoundaryStab_DelayProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:31:39.71401+00:00
-- url     : https://prove2.me/theorems/ae7cf284-f724-4468-aed5-4ade8189cf0b
-- title:
--   The wave equation with delayed boundary feedback (1.1)–(1.5), its regular solutions and the energy E (1.9)
-- statement:
--   Fix a mixed domain $(\Omega, \Gamma_D, \Gamma_N)$ with outer unit normal $\nu$ and surface measure $d\Gamma$, and real parameters $\mu_1, \mu_2, \tau, \xi$. For a function $u(x,t)$ of $x \in \mathbb R^n$ and $t \in \mathbb R$ write $u_t$, $u_{tt}$ for its first and second time derivatives, $\Delta u = \sum_i \partial^2 u/\partial x_i^2$ for its spatial Laplacian, $\nabla u$ for its spatial gradient, and $\partial u/\partial\nu(x,t) = \nabla u(x,t)\cdot\nu(x)$ for its normal derivative.
--
--   A **regular solution** of the problem
--   $$\begin{aligned}
--   &u_{tt}(x,t) - \Delta u(x,t) = 0 && \text{in } \Omega\times(0,+\infty), &(1.1)\\
--   &u(x,t) = 0 && \text{on } \Gamma_D\times(0,+\infty), &(1.2)\\
--   &\tfrac{\partial u}{\partial\nu}(x,t) = -\mu_1 u_t(x,t) - \mu_2 u_t(x,t-\tau) && \text{on } \Gamma_N\times(0,+\infty) &(1.3)
--   \end{aligned}$$
--   is a function $u : \mathbb R^n\times\mathbb R \to \mathbb R$ of class $C^2$ satisfying (1.1)–(1.3). Its initial data (1.4)–(1.5) are $u_0 = u(\cdot,0)$, $u_1 = u_t(\cdot,0)$ and the history $f_0 = u_t$ on $\Gamma_N\times(-\tau,0)$.
--
--   The **energy** of $u$ is
--   $$E(t) := \frac12\int_\Omega\{u_t^2(x,t) + |\nabla u(x,t)|^2\}\,dx + \frac{\xi}{2}\int_{\Gamma_N}\int_0^1 u_t^2(x,t-\tau\rho)\,d\rho\,d\Gamma, \tag{1.9}$$
--   and the **boundary dissipation** at time $t$ is
--   $$\int_{\Gamma_N}\{u_t^2(x,t) + u_t^2(x,t-\tau)\}\,d\Gamma.$$
--
--   The energy $E$ is the standard wave energy plus a term accounting for the delayed velocity on $\Gamma_N$; it is the Lyapunov functional in which Nicaise and Pignotti prove exponential decay when $\mu_2 < \mu_1$.
--
--   **Formalization Note** Solutions are classical: $u$ is one $C^2$ function on $\mathbb R^n\times\mathbb R$, the equations are imposed for $t > 0$, and the values at $t \le 0$ encode the initial data and the history. This is a subclass of the paper's solutions (data that are traces of one $C^2$ function). Time derivatives are `deriv` in $t$, the Laplacian is the sum of the diagonal second derivatives in the standard basis, and every integral has a continuous integrand on a compact set, so no junk value of the Bochner integral arises.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1561, (1.1)–(1.5); p. 1562, (1.9); p. 1569, (3.1)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain

open MeasureTheory

namespace NicaiseDelayWave.BoundaryStab

variable {n : ℕ}

/-- Time derivative `u_t(x, t)`. -/
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
  ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun y => u y t) x
    ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- Normal derivative `∂u/∂ν(x, t) = ∇ₓu(x, t) · ν(x)`. -/
noncomputable def normalDeriv (D : NicaiseDelayWave.Shared.MixedDomain n) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => u y t) x (D.ν x)

/-- A regular (classical) solution of (1.1)–(1.5): a `C²` function `u` of `(x, t) ∈ ℝⁿ × ℝ`
solving the wave equation in `Ω × (0, ∞)`, the Dirichlet condition on `Γ_D × (0, ∞)` and the
delayed feedback `∂u/∂ν(x,t) = -μ₁ u_t(x,t) - μ₂ u_t(x,t-τ)` on `Γ_N × (0, ∞)`. The initial data
(1.4)–(1.5) are the values `u(·,0)`, `u_t(·,0)` and the history `u_t` on `Γ_N × (-τ, 0)`. -/
structure IsRegularSolution (D : NicaiseDelayWave.Shared.MixedDomain n) (μ1 μ2 τ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1 p.2)
  /-- (1.1) -/
  wave : ∀ x ∈ D.Ω, ∀ t > 0, utt u x t - laplacianX u x t = 0
  /-- (1.2) -/
  dirichlet : ∀ x ∈ D.ΓD, ∀ t > 0, u x t = 0
  /-- (1.3) -/
  feedback : ∀ x ∈ D.ΓN, ∀ t > 0,
    normalDeriv D u x t = -μ1 * ut u x t - μ2 * ut u x (t - τ)

/-- The energy (1.9):
`E(t) = ½ ∫_Ω (u_t² + |∇u|²) dx + (ξ/2) ∫_{Γ_N} ∫₀¹ u_t²(x, t - τρ) dρ dΓ`. -/
noncomputable def energy (D : NicaiseDelayWave.Shared.MixedDomain n) (ξ τ : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in D.Ω, (ut u x t ^ 2 + ‖gradient (fun y => u y t) x‖ ^ 2)
    + (ξ / 2) * ∫ x in D.ΓN, (∫ ρ in (0 : ℝ)..1, ut u x (t - τ * ρ) ^ 2) ∂D.σ

/-- The boundary dissipation `∫_{Γ_N} {u_t²(x, t) + u_t²(x, t - τ)} dΓ`. -/
noncomputable def boundaryDissipation (D : NicaiseDelayWave.Shared.MixedDomain n) (τ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in D.ΓN, (ut u x t ^ 2 + ut u x (t - τ) ^ 2) ∂D.σ

end NicaiseDelayWave.BoundaryStab


