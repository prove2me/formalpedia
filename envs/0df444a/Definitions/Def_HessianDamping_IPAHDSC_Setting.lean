-- Prove2me | Definitions.Def_HessianDamping_IPAHDSC_Setting
-- name    : HessianDamping_IPAHDSC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:01.070421+00:00
-- url     : https://prove2.me/theorems/8b10e941-af07-4363-b413-72dd76b6665e
-- title:
--   (IPAHD-SC), pp. 23–27 — the inertial proximal algorithm, q, θ, E₁, v_k, E_k, Z_k
-- statement:
--   Let $H$ be a real Hilbert space, $f:H\to\mathbb R$, and $\mu,\beta,s$ real parameters. This file fixes the objects of Theorem 9 and its proof.
--
--   1. **Strong convexity (Definition 1, p. 19)** is the notion $f-\frac{\mu}{2}\|\cdot\|^2$ convex of the companion file of Theorem 7; it is imported from there, not restated.
--   2. **The algorithm (IPAHD-SC).** Put $c=\frac{2\sqrt{\mu s}}{1+2\sqrt{\mu s}}$ and $\gamma=\frac{\beta\sqrt s+s}{1+2\sqrt{\mu s}}$. A sequence $(x_k)_{k\in\mathbb N}$ is a run of (IPAHD-SC) when, for every $k\ge1$,
--   $$y_k=x_k+(1-c)(x_k-x_{k-1})+\beta\sqrt s\,(1-c)\nabla f(x_k),\qquad x_{k+1}=\operatorname{prox}_{\gamma f}(y_k),$$
--   where $x_{k+1}=\operatorname{prox}_{\gamma f}(y_k)$ means that $x_{k+1}$ minimizes $z\mapsto\gamma f(z)+\frac12\|z-y_k\|^2$. The starting points $x_0,x_1$ are arbitrary.
--   3. **Rates.** $q=\dfrac{1}{1+\frac12\sqrt{\mu s}}$ and $\theta=\dfrac{1}{1+\sqrt{\mu s}}$.
--   4. **Energies.** For a point $x^\star$,
--   $$E_1=f(x_1)-f(x^\star)+\tfrac12\Big\|\sqrt\mu(x_1-x^\star)+\tfrac{1}{\sqrt s}(x_1-x_0)+\beta\nabla f(x_1)\Big\|^2,$$
--   and, for $k\ge1$, $v_k=\sqrt\mu(x_k-x^\star)+\frac{1}{\sqrt s}(x_k-x_{k-1})+\beta\nabla f(x_k)$, $E_k=f(x_k)-f(x^\star)+\frac12\|v_k\|^2$ and $Z_k=2\beta(f(x_k)-f(x^\star))+\sqrt\mu\|x_k-x^\star\|^2$.
--
--   These are the objects in which Theorem 9 and the milestones of its proof are stated; $E_1$ is the constant of the theorem, while $v_k$, $E_k$ and $Z_k$ appear only in the proof.
--
--   **Formalization Note** The proximal step is the published predicate `GoldenRatioVI.Shared.IsProxPoint` applied to $z\mapsto\gamma f(z)$ coerced to `EReal`; no proximal *function* is defined, so the run only asserts that $x_{k+1}$ is a minimizer. ∇f is Mathlib's `gradient`. The objects $y_k$, $v_k$, $E_k$ read $x_{k-1}$ with natural subtraction and are used only for $k\ge1$. No positivity of $\mu,\beta,s$ is built in; the theorems carry it. The file imports `HessianDamping.DINSC.Setting` for `IsStronglyConvex` (Definition 1), so that Theorems 7, 9 and 11 share one definition of strong convexity.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 23, (IPAHD-SC) and Theorem 9 (q, θ, E₁); p. 24, E_k and v_k; p. 27, Z_k

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.IPAHDSC

open GoldenRatioVI.Shared

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The extrapolated point `y_k` of (IPAHD-SC), p. 23:
`y_k = x_k + (1 - 2√(μs)/(1+2√(μs)))(x_k - x_{k-1}) + β√s(1 - 2√(μs)/(1+2√(μs)))∇f(x_k)`.
Used only for `k ≥ 1`. -/
noncomputable def yK (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) (k : ℕ) : H :=
  x k + (1 - 2 * Real.sqrt (μ * s) / (1 + 2 * Real.sqrt (μ * s))) • (x k - x (k - 1)) +
    (β * Real.sqrt s * (1 - 2 * Real.sqrt (μ * s) / (1 + 2 * Real.sqrt (μ * s)))) •
      gradient f (x k)

/-- The proximal parameter `(β√s + s)/(1 + 2√(μs))` of (IPAHD-SC), p. 23. -/
noncomputable def gammaStep (μ β s : ℝ) : ℝ :=
  (β * Real.sqrt s + s) / (1 + 2 * Real.sqrt (μ * s))

/-- A run of (IPAHD-SC), p. 23: for every `k ≥ 1`,
`x_{k+1} = prox_{γ f}(y_k)` with `γ = (β√s + s)/(1 + 2√(μs))`, i.e. `x_{k+1}` minimizes
`z ↦ γ f(z) + ½‖z - y_k‖²`. The initial points `x 0`, `x 1` are free. -/
def IsIPAHDSCRun (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    IsProxPoint (fun z => ((gammaStep μ β s * f z : ℝ) : EReal)) (yK f μ β s x k) (x (k + 1))

/-- `q = 1/(1 + ½√(μs))`, Theorem 9, p. 23. -/
noncomputable def qRate (μ s : ℝ) : ℝ :=
  1 / (1 + 1 / 2 * Real.sqrt (μ * s))

/-- `θ = 1/(1 + √(μs))`, Theorem 9, p. 23. -/
noncomputable def thetaRate (μ s : ℝ) : ℝ :=
  1 / (1 + Real.sqrt (μ * s))

/-- `E₁ = f(x₁) - f(x⋆) + ½‖√μ(x₁ - x⋆) + (1/√s)(x₁ - x₀) + β∇f(x₁)‖²`, Theorem 9, p. 23. -/
noncomputable def E1 (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) (xstar : H) : ℝ :=
  f (x 1) - f xstar +
    1 / 2 * ‖Real.sqrt μ • (x 1 - xstar) + (1 / Real.sqrt s) • (x 1 - x 0) +
      β • gradient f (x 1)‖ ^ 2

/-- `v_k = √μ(x_k - x⋆) + (1/√s)(x_k - x_{k-1}) + β∇f(x_k)`, proof of Theorem 9, p. 24
(used for `k ≥ 1`). -/
noncomputable def vK (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) (xstar : H) (k : ℕ) : H :=
  Real.sqrt μ • (x k - xstar) + (1 / Real.sqrt s) • (x k - x (k - 1)) + β • gradient f (x k)

/-- `E_k = f(x_k) - f(x⋆) + ½‖v_k‖²`, proof of Theorem 9, p. 24 (used for `k ≥ 1`). -/
noncomputable def EK (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) (xstar : H) (k : ℕ) : ℝ :=
  f (x k) - f xstar + 1 / 2 * ‖vK f μ β s x xstar k‖ ^ 2

/-- `Z_k = 2β(f(x_k) - f(x⋆)) + √μ‖x_k - x⋆‖²`, proof of Theorem 9, p. 27. -/
noncomputable def ZK (f : H → ℝ) (μ β : ℝ) (x : ℕ → H) (xstar : H) (k : ℕ) : ℝ :=
  2 * β * (f (x k) - f xstar) + Real.sqrt μ * ‖x k - xstar‖ ^ 2

end HessianDamping.IPAHDSC


