-- Prove2me | Definitions.Def_NonsmoothQN_ExactNorm_Basic
-- name    : NonsmoothQN_ExactNorm_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:20.585976+00:00
-- url     : https://prove2.me/theorems/0af7afce-b9f2-4967-9035-f1035a2a551f
-- title:
--   Algorithm 2.1, Q-linear convergence, §3 — quasi-Newton runs with an exact line search on the Euclidean norm in ℝ²
-- statement:
--   This file fixes the objects of Lewis and Overton's analysis of quasi-Newton methods with an exact line search on the Euclidean norm of the plane.
--
--   **Euclidean norm and gradient.** For $x \in \mathbb R^n$ write $\|x\| = \sqrt{x^T x}$. A vector $g$ is the gradient of $f:\mathbb R^n\to\mathbb R$ at $x$ when $f$ is differentiable at $x$ with derivative $v \mapsto g^T v$. For $f = \|\cdot\|$ and $x \neq 0$ the gradient is
--   $$\nabla f(x) = \|x\|^{-1} x .$$
--
--   **Quasi-Newton direction.** For a matrix $H$ and a point $x$ the direction is $p = -H\,\nabla f(x)$.
--
--   **Angles and orientation in the plane.** For $x, y \in \mathbb R^2$, $\operatorname{cross}(x,y) = x_1 y_2 - x_2 y_1$; it is positive exactly when $y$ is obtained from $x$ by a counterclockwise turn through an angle in $(0,\pi)$. The unsigned angle between nonzero $x$ and $y$ is
--   $$\angle(x,y) = \arccos\frac{x^T y}{\|x\|\,\|y\|} \in [0,\pi].$$
--
--   **Q-linear convergence** (p. 141). A real sequence $(\tau_k)$ converges to $\mu$ Q-linearly with rate $r$ when $\tau_k \to \mu$ and $|\tau_{k+1}-\mu|/|\tau_k-\mu| \to r$.
--
--   **The angle map.** $g(s) = \sqrt{(1-s)/2}$, the map of the proof of Theorem 3.2 that sends $\sin\theta_k$ to $\sin\theta_{k+1}$.
--
--   **Runs of Algorithm 2.1 with an exact line search on $f = \|\cdot\|$ in $\mathbb R^2$.** A run is a sequence of points $x_0, x_1, \dots \in \mathbb R^2$, matrices $H_0, H_1, \dots$ and steps $t_0, t_1, \dots$ such that
--
--   1. $x_0 \neq 0$ (so $f$ is differentiable at $x_0$);
--   2. every $H_k$ is symmetric positive definite;
--   3. every $t_k > 0$;
--   4. with $p_k = -H_k \nabla f(x_k)$, the step is exact: $t_k$ minimizes $\tau \mapsto \|x_k + \tau p_k\|$ over $\tau\in\mathbb R$;
--   5. $x_{k+1} = x_k + t_k p_k$;
--   6. whenever $x_{k+1} \neq 0$ (the method has not stopped), $H_{k+1}$ satisfies the secant condition $H_{k+1} y_k = t_k p_k$ with $y_k = \nabla f(x_{k+1}) - \nabla f(x_k)$.
--
--   Any positive definite update satisfying the secant condition is allowed; BFGS (2.2) is one choice. Since $0$ is the only point where the norm is not differentiable and $\nabla f \neq 0$ elsewhere, Algorithm 2.1 stops exactly when some iterate is $0$; non-termination is therefore the separate hypothesis $x_k \neq 0$ for all $k$, carried by the theorems.
--
--   **Formalization Note.** Vectors are `Fin n → ℝ` and the Euclidean norm is written out as $\sqrt{x^T x}$ (`eucNorm`), because the default norm on `Fin n → ℝ` is the sup norm. The gradient of the norm is the explicit formula $\|x\|^{-1}x$; at $x = 0$ Lean's $0^{-1}=0$ gives the junk value $0$, which is never used because the secant field is guarded by $x_{k+1}\neq 0$ and the theorems assume non-termination. Positive definiteness is `Matrix.PosDef`, which includes symmetry. The exact line search minimizes over all real $\tau$; for $x_k \neq 0$ the minimizer is unique and positive because $p_k$ is a descent direction, so this is the same as minimizing over $\tau > 0$. In the Q-linear ratio, division by $0$ would give $0$; under non-termination the denominators are positive.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 139–142, Algorithm 2.1 (p. 140), Q-linear convergence (§2, p. 141), exact line search and the norm (§3, p. 141), ∇f(x) = ‖x‖⁻¹x (§3.1, p. 142)

import Mathlib

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

/-- The Euclidean norm `‖x‖ = √(xᵀx)` on `ℝⁿ`, written explicitly because the default norm on
`Fin n → ℝ` is the sup norm. -/
noncomputable def eucNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-- `g` is the (Euclidean) gradient of `f` at `x`: `f` is differentiable at `x` and its
derivative is `v ↦ gᵀv`. -/
def IsGradAt {n : ℕ} (f : (Fin n → ℝ) → ℝ) (g x : Fin n → ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧ ∀ v, fderiv ℝ f x v = g ⬝ᵥ v

/-- The gradient `∇f(x) = ‖x‖⁻¹ x` of the Euclidean norm at `x ≠ 0` (p. 142). At `x = 0`, where
the norm is not differentiable, Lean's `0⁻¹ = 0` gives the junk value `0`; every use is guarded
by `x ≠ 0`. -/
noncomputable def gradNorm {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := (eucNorm x)⁻¹ • x

/-- The quasi-Newton direction `p = −H ∇f(x)` of Algorithm 2.1 for `f = ‖·‖`. -/
noncomputable def qnDir {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  -(H *ᵥ gradNorm x)

/-- The orientation sign of a pair of plane vectors: `x₀ y₁ − x₁ y₀`, positive when `y` lies
counterclockwise of `x` (by an angle in `(0, π)`). -/
def cross (x y : Fin 2 → ℝ) : ℝ := x 0 * y 1 - x 1 * y 0

/-- The unsigned angle in `[0, π]` between two nonzero vectors,
`arccos (xᵀy / (‖x‖ ‖y‖))`. -/
noncomputable def turnAngle {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.arccos ((x ⬝ᵥ y) / (eucNorm x * eucNorm y))

/-- Q-linear convergence (p. 141): `τ_k → μ` and `|τ_{k+1} − μ| / |τ_k − μ| → r`. -/
def IsQLinear (τ : ℕ → ℝ) (μ r : ℝ) : Prop :=
  Tendsto τ atTop (𝓝 μ) ∧
    Tendsto (fun k => |τ (k + 1) - μ| / |τ k - μ|) atTop (𝓝 r)

/-- The map `s ↦ √((1 − s)/2)` of the proof of Theorem 3.2 (p. 142), sending `sin θ_k` to
`sin θ_{k+1}`. -/
noncomputable def angleMap (s : ℝ) : ℝ := Real.sqrt ((1 - s) / 2)

/-- A run of Algorithm 2.1 (quasi-Newton method) with an exact line search, applied to the
Euclidean norm `f = ‖·‖` on `ℝ²`: iterates `x k`, positive definite (hence symmetric) matrices
`H k`, and step sizes `t k > 0` with
* `x 0 ≠ 0` (`f` is differentiable at `x₀`);
* `x (k+1) = x k + t k • p k`, `p k = −H k ∇f(x k)`;
* exactness: `t k` minimizes `τ ↦ ‖x k + τ p k‖` over all real `τ`;
* the secant condition `H (k+1) y k = t k p k`, `y k = ∇f(x (k+1)) − ∇f(x k)`, whenever the
  method has not stopped at `x (k+1)` (i.e. `x (k+1) ≠ 0`).
Any positive definite update satisfying the secant condition is allowed, not only BFGS. -/
structure IsExactNormRun (x : ℕ → Fin 2 → ℝ) (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℕ → ℝ) : Prop where
  start : x 0 ≠ 0
  posDef : ∀ k, (H k).PosDef
  step_pos : ∀ k, 0 < t k
  exact : ∀ k (τ : ℝ),
    eucNorm (x k + t k • qnDir (H k) (x k)) ≤ eucNorm (x k + τ • qnDir (H k) (x k))
  next : ∀ k, x (k + 1) = x k + t k • qnDir (H k) (x k)
  secant : ∀ k, x (k + 1) ≠ 0 →
    H (k + 1) *ᵥ (gradNorm (x (k + 1)) - gradNorm (x k)) = t k • qnDir (H k) (x k)

end NonsmoothQN.ExactNorm


