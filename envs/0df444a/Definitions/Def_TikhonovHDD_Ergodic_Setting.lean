-- Prove2me | Definitions.Def_TikhonovHDD_Ergodic_Setting
-- name    : TikhonovHDD_Ergodic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:26.648776+00:00
-- url     : https://prove2.me/theorems/cf12cd2f-8d50-4870-87a8-e7d6c642809f
-- title:
--   System (5), the General assumption, and h_{x*} (pp. 2, 16)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0\in\mathbb R$, $\alpha,\beta\in\mathbb R$ and $u_0,v_0\in\mathcal H$. This file defines the dynamical system studied by Boţ, Csetnek and László and the standing hypotheses on its data.
--
--   1. **General assumption on $g$.** $g:\mathcal H\to\mathbb R$ is convex and twice Fréchet differentiable (both $g$ and its gradient $\nabla g$ are Fréchet differentiable), $\nabla g$ is Lipschitz continuous on bounded sets (on every closed ball centred at the origin, with a constant depending on the ball), and $\operatorname{argmin} g\neq\emptyset$.
--   2. **General assumption on $\epsilon$.** $\epsilon:[t_0,+\infty)\to[0,+\infty)$ is nonincreasing, of class $C^1$ with derivative $\dot\epsilon$, and $\lim_{t\to+\infty}\epsilon(t)=0$.
--   3. **Global $C^2$-solution of (5).** A curve $x:[t_0,+\infty)\to\mathcal H$ with velocity $\dot x$ and continuous acceleration $\ddot x$ solves
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0\quad(t\ge t_0),\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0 .
--   $$
--   Here $\nabla^2 g(x)v$ is the derivative of $\nabla g$ at $x$ applied to $v$.
--   4. **The anchor function.** For $x^*\in\mathcal H$, $h_{x^*}(t)=\tfrac12\|x(t)-x^*\|^2$, with derivative $\dot h_{x^*}(t)=\langle\dot x(t),x(t)-x^*\rangle$.
--
--   System (5) combines the Nesterov-type vanishing damping $\frac{\alpha}{t}\dot x$, a Hessian-driven damping term $\beta\nabla^2g(x)\dot x$, and a Tikhonov regularization term $\epsilon(t)x$; all results of §4 of the paper are statements about its solutions.
--
--   **Formalization Note** Trajectories and parameter functions are maps $\mathbb R\to\mathcal H$ (resp. $\mathbb R\to\mathbb R$) whose values before $t_0$ are irrelevant; derivatives are taken within $[t_0,+\infty)$, so they are one-sided at $t_0$. The derivative maps $\dot x$, $\ddot x$, $\dot\epsilon$ are explicit arguments tied to $x$, $\dot x$, $\epsilon$ by derivative hypotheses. The paper's standing restriction $\alpha\ge3$, $\beta\ge0$ is not part of the solution predicate: each theorem states its own hypotheses on $\alpha$ and $\beta$. $\dot h_{x^*}$ is defined directly as the inner product; that it is the derivative of $h_{x^*}$ follows from the chain rule.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 2, (5) and General assumption; p. 16, Lemma 4.1 (h_{x∗}); p. 17, proof of Lemma 4.1 (ḣ_{x∗})

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve

namespace TikhonovHDD.Ergodic

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The first bullet of the General assumption (p. 2): `g : H → ℝ` is convex and twice Fréchet
differentiable (`g` and its gradient `∇g` are differentiable), `∇g` is Lipschitz continuous on
bounded sets (on every closed ball around the origin), and `argmin g ≠ ∅`. -/
def GeneralAssumptionG (g : H → ℝ) : Prop :=
  ConvexOn ℝ univ g ∧ Differentiable ℝ g ∧ Differentiable ℝ (gradient g) ∧
    (∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (gradient g) (Metric.closedBall 0 R)) ∧
    (TikhonovHDD.Strong.argminSet g).Nonempty

/-- The second bullet of the General assumption (p. 2): `ε : [t₀, +∞) → [0, +∞)` is
nonincreasing, of class `C¹` with derivative map `ε'` (one-sided at `t₀`), and
`ε(t) → 0` as `t → +∞`. Values of `ε` and `ε'` before `t₀` are irrelevant. -/
def GeneralAssumptionEps (t₀ : ℝ) (ε ε' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ici t₀, HasDerivWithinAt ε (ε' t) (Ici t₀) t) ∧ ContinuousOn ε' (Ici t₀) ∧
    (∀ t ∈ Ici t₀, 0 ≤ ε t) ∧ AntitoneOn ε (Ici t₀) ∧ Tendsto ε atTop (𝓝 0)

/-- `x`, with velocity map `xd` (`ẋ`) and acceleration map `xdd` (`ẍ`), is a global
`C²`-solution of system (5) (p. 2):
`ẍ(t) + (α/t)ẋ(t) + β∇²g(x(t))ẋ(t) + ∇g(x(t)) + ε(t)x(t) = 0` for `t ≥ t₀`,
`x(t₀) = u₀`, `ẋ(t₀) = v₀`. Derivatives are taken within `[t₀, +∞)` (one-sided at `t₀`),
`ẍ` is continuous on `[t₀, +∞)`, and `∇²g(x)v` is the Fréchet derivative of `∇g` at `x`
applied to `v`. Values for `t < t₀` are irrelevant. -/
def IsSolution (g : H → ℝ) (α β : ℝ) (ε : ℝ → ℝ) (t₀ : ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) :
    Prop :=
  (∀ t ∈ Ici t₀,
      HasDerivWithinAt x (xd t) (Ici t₀) t ∧
      HasDerivWithinAt xd (xdd t) (Ici t₀) t ∧
      xdd t + (α / t) • xd t + β • (fderiv ℝ (gradient g) (x t)) (xd t)
        + gradient g (x t) + ε t • x t = 0) ∧
    ContinuousOn xdd (Ici t₀) ∧ x t₀ = u₀ ∧ xd t₀ = v₀

/-- `h_{x⋆}(t) = ½‖x(t) − x⋆‖²` (Lemma 4.1, p. 16). -/
noncomputable def hFun (x : ℝ → H) (xstar : H) (t : ℝ) : ℝ :=
  1 / 2 * ‖x t - xstar‖ ^ 2

/-- `ḣ_{x⋆}(t) = ⟨ẋ(t), x(t) − x⋆⟩`, the derivative of `h_{x⋆}` along a trajectory with
velocity map `xd` (proof of Lemma 4.1, p. 17). -/
noncomputable def hDot (x xd : ℝ → H) (xstar : H) (t : ℝ) : ℝ :=
  inner ℝ (xd t) (x t - xstar)

end TikhonovHDD.Ergodic


