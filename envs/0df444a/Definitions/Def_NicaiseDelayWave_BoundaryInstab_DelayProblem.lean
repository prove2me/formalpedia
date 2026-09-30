-- Prove2me | Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem
-- name    : NicaiseDelayWave_BoundaryInstab_DelayProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T20:39:51.851896+00:00
-- url     : https://prove2.me/theorems/33b4d1ba-4cc8-41b7-84c7-039ee49814aa
-- title:
--   Complex classical solutions of the wave equation with delayed boundary feedback (1.1)–(1.3), standard energy (3.7), and the functionals q₀, q₁ of (5.11)
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N, \sigma)$ be a mixed domain with outer unit normal $\nu$, let $\mu_1, \mu_2, \tau$ be real numbers, and let $u : \mathbb R^n \times \mathbb R \to \mathbb C$.
--
--   1. **Derivatives.** $u_t$ and $u_{tt}$ are the first and second partial derivatives of $u$ in $t$; the Laplacian of a real- or complex-valued $f$ on $\mathbb R^n$ is $\Delta f = \sum_{i=1}^n \partial_i^2 f$; the normal derivative is $\frac{\partial f}{\partial \nu}(x) = Df(x)\,\nu(x)$, where $Df(x)$ is the derivative of $f$ *within* $\overline\Omega$ (so it is the one-sided derivative at boundary points).
--   2. **Classical solution.** $u$ is a classical solution of problem (1.1)–(1.3) with delay $\tau$ if $u$ is $C^2$ on $\Omega \times \mathbb R$, $C^1$ on $\overline\Omega \times \mathbb R$, and
--   $$\begin{cases} u_{tt}(x,t) - \Delta u(x,t) = 0 & \text{in } \Omega \times (0,+\infty),\\ u(x,t) = 0 & \text{on } \Gamma_D \times (0,+\infty),\\ \dfrac{\partial u}{\partial \nu}(x,t) = -\mu_1 u_t(x,t) - \mu_2 u_t(x,t-\tau) & \text{on } \Gamma_N \times (0,+\infty). \end{cases}$$
--   The initial data (1.4)–(1.5) — $u(\cdot,0)$, $u_t(\cdot,0)$ and the history $u_t$ on $\Gamma_N \times (-\tau, 0)$ — are the values of $u$ itself at times $t \le 0$.
--   3. **Standard energy** (3.7): $$\mathcal E(t) = \frac12 \int_\Omega \big( |u_t(x,t)|^2 + |\nabla u(x,t)|^2 \big)\,dx, \qquad |\nabla u|^2 = \sum_{i=1}^n |\partial_i u|^2 .$$
--   4. **Admissible class** $\mathcal V$: real functions $w$ on $\mathbb R^n$ that are $C^2$ in $\Omega$, $C^1$ on $\overline\Omega$, and vanish on $\Gamma_D$. It stands in for the space $H^1_{\Gamma_D}(\Omega)$ of the paper.
--   5. **The functionals** (5.11) and (5.15): for real $w$ and $s \in \mathbb R$,
--   $$q_0(w) = \int_{\Gamma_N} |w|^2\,d\Gamma, \qquad q_1(w) = \int_\Omega |\nabla w|^2\,dx, \qquad B_s(w) = s\,q_0(w) + \sqrt{s^2 q_0(w)^2 + 4 q_1(w)} .$$
--
--   These are the objects of §5.1 of Nicaise and Pignotti (2006): the spectral construction of solutions with constant standard energy is carried out for this problem, and $2b = B_s(\varphi)$ with $s = \sqrt{\mu_2^2-\mu_1^2}$ is the frequency of the page's solution in case (b).
--
--   **Formalization Note** Solutions are complex-valued, as the page's $u = e^{\lambda t}\varphi$, $\lambda \in \mathbb C$, are; the paper does not state the value field of its solutions. The gradient square of a complex function is the sum of the squared moduli of its partial derivatives. The normal derivative uses the derivative within $\overline\Omega$, since the solutions are only $C^1$ up to the boundary (eigenfunctions of mixed problems on $C^2$ domains are not $C^2(\overline\Omega)$ in general). The admissible class $\mathcal V$ replaces the Sobolev space $H^1_{\Gamma_D}(\Omega)$, which is not available in Mathlib.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1561, (1.1)–(1.5); p. 1571, (3.7); pp. 1579–1581, (5.1), (5.11), (5.15)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain

open MeasureTheory

namespace NicaiseDelayWave.BoundaryInstab

variable {n : ℕ}

/-- Time derivative `u_t(x, t)` of a complex-valued function of `(x, t)`. -/
noncomputable def ut (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℂ :=
  deriv (fun s => u x s) t

/-- Second time derivative `u_tt(x, t)`. -/
noncomputable def utt (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℂ :=
  deriv (fun s => ut u x s) t

/-- The Laplacian `Δf(x) = ∑ᵢ ∂²f/∂xᵢ²(x)` of a (real- or complex-valued) function on `ℝⁿ`. -/
noncomputable def laplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) : F :=
  ∑ i : Fin n, iteratedFDeriv ℝ 2 f x
    ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- The normal derivative `∂f/∂ν(x)`, the derivative of `f` within `closure Ω` at `x` in the
direction of the outer unit normal `ν(x)`. -/
noncomputable def normalDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : NicaiseDelayWave.Shared.MixedDomain n) (f : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) : F :=
  fderivWithin ℝ f (closure D.Ω) x (D.ν x)

/-- A classical (complex-valued) solution of (1.1)–(1.3) = (5.1) with delay `τ`: `u` is `C²` in
`Ω × ℝ` and `C¹` up to the boundary, solves `u_tt - Δu = 0` in `Ω × (0, ∞)`, `u = 0` on
`Γ_D × (0, ∞)` and `∂u/∂ν(x,t) = -μ₁ u_t(x,t) - μ₂ u_t(x,t-τ)` on `Γ_N × (0, ∞)`. The initial
data (1.4)–(1.5) are the values of `u` at `t ≤ 0`. -/
structure IsClassicalSolution (D : NicaiseDelayWave.Shared.MixedDomain n) (μ1 μ2 τ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ) : Prop where
  contDiffOn_interior :
    ContDiffOn ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1 p.2) (D.Ω ×ˢ Set.univ)
  contDiffOn_closure :
    ContDiffOn ℝ 1 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1 p.2)
      (closure D.Ω ×ˢ Set.univ)
  /-- (1.1) -/
  wave : ∀ x ∈ D.Ω, ∀ t > 0, utt u x t - laplacian (fun y => u y t) x = 0
  /-- (1.2) -/
  dirichlet : ∀ x ∈ D.ΓD, ∀ t > 0, u x t = 0
  /-- (1.3) -/
  feedback : ∀ x ∈ D.ΓN, ∀ t > 0,
    normalDeriv D (fun y => u y t) x = -(μ1 : ℂ) * ut u x t - (μ2 : ℂ) * ut u x (t - τ)

/-- The standard energy (3.7), for complex-valued `u`:
`𝓔(t) = ½ ∫_Ω (|u_t(x,t)|² + |∇u(x,t)|²) dx`, with `|∇u|² = ∑ᵢ |∂ᵢu|²`. -/
noncomputable def stdEnergy (D : NicaiseDelayWave.Shared.MixedDomain n) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in D.Ω, (‖ut u x t‖ ^ 2 +
    ∑ i : Fin n, ‖fderiv ℝ (fun y => u y t) x (EuclideanSpace.single i 1)‖ ^ 2)

/-- The classical admissible class standing in for `H¹_{Γ_D}(Ω)`: real functions that are `C²`
in `Ω`, `C¹` up to the boundary, and vanish on `Γ_D`. -/
def admissible (D : NicaiseDelayWave.Shared.MixedDomain n) : Set (EuclideanSpace ℝ (Fin n) → ℝ) :=
  {w | ContDiffOn ℝ 2 w D.Ω ∧ ContDiffOn ℝ 1 w (closure D.Ω) ∧ ∀ x ∈ D.ΓD, w x = 0}

/-- (5.11): `q₀(w) = ∫_{Γ_N} |w|² dΓ`. -/
noncomputable def q0 (D : NicaiseDelayWave.Shared.MixedDomain n) (w : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x in D.ΓN, w x ^ 2 ∂D.σ

/-- (5.11): `q₁(w) = ∫_Ω |∇w|² dx`. -/
noncomputable def q1 (D : NicaiseDelayWave.Shared.MixedDomain n) (w : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x in D.Ω, ‖gradient w x‖ ^ 2

/-- The functional minimised in (5.15):
`B_s(w) = s q₀(w) + √(s² q₀(w)² + 4 q₁(w))`, with `s = √(μ₂² - μ₁²)` in the paper. -/
noncomputable def functionalB (D : NicaiseDelayWave.Shared.MixedDomain n) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  s * q0 D w + Real.sqrt (s ^ 2 * q0 D w ^ 2 + 4 * q1 D w)

end NicaiseDelayWave.BoundaryInstab


