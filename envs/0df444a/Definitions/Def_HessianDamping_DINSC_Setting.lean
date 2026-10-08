-- Prove2me | Definitions.Def_HessianDamping_DINSC_Setting
-- name    : HessianDamping_DINSC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:10.425979+00:00
-- url     : https://prove2.me/theorems/6643a494-a0df-4bf4-b58b-5b328c8f004d
-- title:
--   Definition 1 and (19), pp. 19–20 — μ-strong convexity, solutions of (DIN)_{2√μ,β}, and the functions E and Z of the proof of Theorem 7
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $f:\mathcal H\to\mathbb R$.
--
--   1. **Strong convexity (Definition 1).** For $\mu>0$, $f$ is *$\mu$-strongly convex* if $f-\frac{\mu}{2}\|\cdot\|^2$ is convex on $\mathcal H$.
--   2. **Solution trajectory of (19).** Given $\mu$, a constant $\beta\in\mathbb R$ and $t_0$, a map $x:[t_0,+\infty[\to\mathcal H$ with velocity $\dot x$ and acceleration $\ddot x$ is a solution of
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\beta\nabla^2 f(x(t))\dot x(t)+\nabla f(x(t))=0\qquad(t\ge t_0),$$
--   where the derivatives at $t_0$ are one-sided (right) derivatives.
--   3. **The Lyapunov function** of the proof of Theorem 7, for a minimizer $x^\star$ of $f$:
--   $$\mathcal E(t):=f(x(t))-\min_{\mathcal H}f+\tfrac12\big\|\sqrt{\mu}(x(t)-x^\star)+\dot x(t)+\beta\nabla f(x(t))\big\|^2 .$$
--   4. **The auxiliary function** of part (ii) of that proof:
--   $$Z(t):=2\beta\big(f(x(t))-f(x^\star)\big)+\sqrt{\mu}\,\|x(t)-x^\star\|^2 .$$
--
--   These are the objects in which Theorem 7 and the steps of its proof are stated.
--
--   **Formalization Note.** A trajectory is a triple of maps $x,\dot x,\ddot x:\mathbb R\to\mathcal H$; the solution predicate asks, at every $t\ge t_0$, that $x$ have derivative $\dot x(t)$ and $\dot x$ have derivative $\ddot x(t)$ within $[t_0,+\infty[$, and that the equation hold. Values for $t<t_0$ are irrelevant. The Hessian applied to $\dot x(t)$ is the Fréchet derivative of $\nabla f$ at $x(t)$ applied to $\dot x(t)$. The bound $\mu>0$ is a separate hypothesis of every theorem, and $\min_{\mathcal H} f$ is written $f(x^\star)$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 19, Definition 1 and (19); p. 20, definition of E in the proof of Theorem 7; p. 21, definition of Z in the proof of Theorem 7 (ii)

import Mathlib

namespace HessianDamping.DINSC

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Definition 1 (p. 19): `f : H → ℝ` is `μ`-strongly convex if `f − (μ/2)‖·‖²` is convex.
The positivity `0 < μ` of the definition is a separate hypothesis wherever this is used. -/
def IsStronglyConvex (f : H → ℝ) (μ : ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun x => f x - μ / 2 * ‖x‖ ^ 2)

/-- `x : [t₀, +∞[ → H`, with derivative maps `xd` (the velocity `ẋ`) and `xdd` (the
acceleration `ẍ`), is a solution trajectory of (19):
`ẍ(t) + 2√μ ẋ(t) + β ∇²f(x(t)) ẋ(t) + ∇f(x(t)) = 0`, with a constant `β`.
The derivatives are one-sided at `t₀` (taken within `[t₀, +∞[`); the Hessian applied to
`ẋ(t)` is the Fréchet derivative of `∇f` at `x(t)` applied to `ẋ(t)`. Values of `x`, `xd`,
`xdd` for `t < t₀` are irrelevant. -/
def IsSolution19 (f : H → ℝ) (μ β t₀ : ℝ) (x xd xdd : ℝ → H) : Prop :=
  ∀ t ∈ Ici t₀,
    HasDerivWithinAt x (xd t) (Ici t₀) t ∧
    HasDerivWithinAt xd (xdd t) (Ici t₀) t ∧
    xdd t + (2 * Real.sqrt μ) • xd t + β • (fderiv ℝ (gradient f) (x t)) (xd t)
      + gradient f (x t) = 0

/-- The Lyapunov function of the proof of Theorem 7 (p. 20):
`E(t) := f(x(t)) − f(x⋆) + ½‖√μ (x(t) − x⋆) + ẋ(t) + β ∇f(x(t))‖²`
(the page writes `min_H f` for `f(x⋆)`). -/
noncomputable def lyap (f : H → ℝ) (μ β : ℝ) (xstar : H) (x xd : ℝ → H) (t : ℝ) : ℝ :=
  f (x t) - f xstar
    + 1 / 2 * ‖Real.sqrt μ • (x t - xstar) + xd t + β • gradient f (x t)‖ ^ 2

/-- The function of the proof of Theorem 7 (ii) (p. 21):
`Z(t) := 2β (f(x(t)) − f(x⋆)) + √μ ‖x(t) − x⋆‖²`. -/
noncomputable def Zfun (f : H → ℝ) (μ β : ℝ) (xstar : H) (x : ℝ → H) (t : ℝ) : ℝ :=
  2 * β * (f (x t) - f xstar) + Real.sqrt μ * ‖x t - xstar‖ ^ 2

end HessianDamping.DINSC


