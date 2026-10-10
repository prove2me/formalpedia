-- Prove2me | Definitions.Def_NAGFlow_Implicit_Setting
-- name    : NAGFlow_Implicit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:19.71098+00:00
-- url     : https://prove2.me/theorems/fd5c76c8-cbb4-46d2-9b51-3a1d50fa4d08
-- title:
--   (2) p. 2, (72)–(74) p. 16 — the class S¹_μ, the implicit scheme with its γ equation, and the Lyapunov function ℒ_k
-- statement:
--   This file fixes the objects of §4 of Luo and Chen, *From differential equation solvers to accelerated first-order methods for convex optimization*.
--
--   Let $V$ be a real Hilbert space with inner product $(\cdot,\cdot)$ and norm $\|\cdot\|$, and let $f:V\to\mathbb R$.
--
--   1. **The class $\mathcal S^1_\mu$** (p. 2, (2) with $\Omega=V$). Given $\mu\ge 0$, $f\in\mathcal S^1_\mu$ if $f$ is continuously differentiable, with gradient $\nabla f$, and
--   $$f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ \ge\ \frac\mu2\|x-y\|^2\qquad\forall x,y\in V.$$
--   For $\mu=0$ this is convexity; for $\mu>0$, strong convexity.
--
--   2. **The Lyapunov function** (74). For a point $x^*$, sequences $(x_k),(v_k)$ in $V$ and a real sequence $(\gamma_k)$,
--   $$\mathcal L_k:=f(x_k)-f(x^*)+\frac{\gamma_k}2\|v_k-x^*\|^2 .$$
--
--   3. **One step of the implicit scheme** (72)–(73). Step $k$ holds if $\alpha_k>0$ and
--   $$\frac{x_{k+1}-x_k}{\alpha_k}=v_{k+1}-x_{k+1},\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(x_{k+1}-v_{k+1})-\frac1{\gamma_k}\nabla f(x_{k+1}),\qquad \frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_{k+1}.$$
--
--   4. **A run** of the scheme is a choice of sequences $(\alpha_k),(\gamma_k),(x_k),(v_k)$ with $\gamma_0>0$ such that every step $k\in\mathbb N$ holds.
--
--   The scheme is the fully implicit (backward Euler) discretization of the NAG flow of §3 together with its parameter equation $\gamma'=\mu-\gamma$; $\mathcal L_k$ is the discrete analogue of the flow's Lyapunov function.
--
--   **Formalization Note.** $V$ carries `InnerProductSpace ℝ V` and `CompleteSpace V`; by the Riesz identification the duality pairing $\langle\cdot,\cdot\rangle$ and the inner product $(\cdot,\cdot)$ are both the real inner product, and the dual norm is the norm. The gradient is an explicit map `gradf` with `HasGradientAt f (gradf x) x` at every point, and "continuously differentiable" is continuity of `gradf`. The step equations are kept in the page's difference-quotient form, with vector division by $\alpha_k$ written as scalar multiplication by $1/\alpha_k$; they are equations on given sequences, and no existence of a solution of the implicit system is asserted.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2) p. 2; (72), (73), (74) p. 16

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.Implicit

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The Lyapunov function (74), p. 16:
`ℒ_k := f(x_k) - f(x*) + γ_k/2 ‖v_k - x*‖²`. -/
noncomputable def lyap (f : V → ℝ) (xstar : V) (x v : ℕ → V) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  f (x k) - f xstar + γ k / 2 * ‖v k - xstar‖ ^ 2

/-- Step `k` of the implicit scheme (72) together with the implicit parameter equation (73),
p. 16, written in the page's difference-quotient form:
`α_k > 0`,
`(x_{k+1} - x_k)/α_k = v_{k+1} - x_{k+1}`,
`(v_{k+1} - v_k)/α_k = (μ/γ_k)(x_{k+1} - v_{k+1}) - (1/γ_k)∇f(x_{k+1})`,
`(γ_{k+1} - γ_k)/α_k = μ - γ_{k+1}`.
The equations are implicit and are kept as equations; nothing asserts that a solution exists. -/
structure IsImplicitStep (gradf : V → V) (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V) (k : ℕ) :
    Prop where
  alpha_pos : 0 < α k
  x_eq : (1 / α k) • (x (k + 1) - x k) = v (k + 1) - x (k + 1)
  v_eq : (1 / α k) • (v (k + 1) - v k)
    = (μ / γ k) • (x (k + 1) - v (k + 1)) - (1 / γ k) • gradf (x (k + 1))
  gamma_eq : (γ (k + 1) - γ k) / α k = μ - γ (k + 1)

/-- A run of the implicit scheme (72)–(73), p. 16: `γ₀ > 0` and every step `k ∈ ℕ` is a step
of (72)–(73). -/
structure IsImplicitRun (gradf : V → V) (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V) : Prop where
  gamma0_pos : 0 < γ 0
  step : ∀ k : ℕ, IsImplicitStep gradf μ α γ x v k

end NAGFlow.Implicit


