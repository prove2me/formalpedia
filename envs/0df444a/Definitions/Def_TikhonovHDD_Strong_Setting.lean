-- Prove2me | Definitions.Def_TikhonovHDD_Strong_Setting
-- name    : TikhonovHDD_Strong_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:12.57153+00:00
-- url     : https://prove2.me/theorems/d6cefb51-b00b-49f5-b000-d21c1be0c99f
-- title:
--   System (5), the General assumption, min g, and the minimum-norm minimizer (p. 2, p. 21)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. This file fixes the objects in which every statement of the mission is written.
--
--   1. **Minimizers and minimal value.** For $g:\mathcal H\to\mathbb R$, $\operatorname{argmin} g=\{x\in\mathcal H : g(x)\le g(y)\ \text{for all } y\in\mathcal H\}$, and $\min g$ is the infimum of the values of $g$. When $\operatorname{argmin} g\neq\emptyset$ this infimum is attained and equals $g(\hat x)$ for every $\hat x\in\operatorname{argmin} g$.
--   2. **General assumption.** Given $t_0\in\mathbb R$, a function $g:\mathcal H\to\mathbb R$ and a function $\epsilon:[t_0,+\infty)\to\mathbb R$ with derivative $\dot\epsilon$, the General assumption says:
--      - $g$ is convex and twice Fréchet differentiable, its gradient $\nabla g$ is Lipschitz continuous on bounded sets, and $\operatorname{argmin} g\neq\emptyset$;
--      - $\epsilon$ takes values in $[0,+\infty)$, is nonincreasing and of class $C^1$ on $[t_0,+\infty)$, and $\lim_{t\to+\infty}\epsilon(t)=0$.
--   3. **Solutions of (5).** For real parameters $\alpha,\beta$, a time $t_0$ and initial data $u_0,v_0\in\mathcal H$, a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\quad t\ge t_0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0, \tag{5}
--   $$
--   is a curve $x:[t_0,+\infty)\to\mathcal H$, twice differentiable with continuous second derivative on $[t_0,+\infty)$, which satisfies the equation at every $t\ge t_0$ together with the two initial conditions.
--   4. **Minimum-norm minimizer.** $x^*$ is the element of minimum norm of $\operatorname{argmin} g$: $x^*\in\operatorname{argmin} g$ and $\|x^*\|\le\|z\|$ for every $z\in\operatorname{argmin} g$. Since $\operatorname{argmin} g$ is nonempty, closed and convex, such an element exists and is unique.
--
--   These are the model of Boţ, Csetnek and László: the inertial dynamics with vanishing viscous damping $\alpha/t$, Hessian driven damping of strength $\beta$, and a Tikhonov regularization term $\epsilon(t)x(t)$, whose trajectories are studied in relation to the minimizer of $g$ of minimum norm.
--
--   **Formalization Note** Curves are maps $\mathbb R\to\mathcal H$ whose values before $t_0$ are irrelevant. The velocity $\dot x$, the acceleration $\ddot x$ and $\dot\epsilon$ are passed as explicit maps, tied to $x$, $\dot x$ and $\epsilon$ by derivatives taken within $[t_0,+\infty)$ (one-sided at $t_0$); continuity of $\ddot x$ and of $\dot\epsilon$ on $[t_0,+\infty)$ gives the $C^2$ and $C^1$ requirements. "Twice Fréchet differentiable" is: $g$ and $\nabla g$ are Fréchet differentiable; $\nabla^2 g(x)v$ is the Fréchet derivative of $\nabla g$ at $x$ applied to $v$. "Lipschitz on bounded sets" is: Lipschitz on every closed ball centred at $0$. $\min g$ is `sInf (Set.range g)`. The restrictions $t_0>0$, $\beta\ge0$ and the bound on $\alpha$ that accompany (5) on p. 2 are not built into these predicates; every theorem that uses them states them as hypotheses, with the bound on $\alpha$ that the theorem itself requires.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 2, (5) and General assumption; p. 21, Theorem 4.4 (x* the element of minimum norm of argmin g)

import Mathlib

namespace TikhonovHDD.Strong

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `argmin g = {x ∈ H : g x ≤ g y for every y ∈ H}`, the set of global minimizers of `g`. -/
def argminSet (g : H → ℝ) : Set H :=
  {x | ∀ y, g x ≤ g y}

/-- `min g`, the minimal value of `g`, as the infimum of the range of `g`. When `argmin g` is
nonempty (as under the General assumption) this infimum is attained and equals `g x̂` for every
`x̂ ∈ argmin g`. -/
noncomputable def minValue (g : H → ℝ) : ℝ :=
  sInf (Set.range g)

/-- The General assumption of Boţ, Csetnek, László (arXiv:1911.12845v2, p. 2):

* `g : H → ℝ` is convex and twice Fréchet differentiable (`g` and `∇g` are Fréchet
  differentiable), `∇g` is Lipschitz continuous on every bounded set (on every closed ball
  centred at `0`), and `argmin g ≠ ∅`;
* `ε : [t₀, +∞) → [0, +∞)` is nonincreasing, of class `C¹` with derivative map `ε'`
  (one-sided at `t₀`), and `ε(t) → 0` as `t → +∞`. Values of `ε`, `ε'` before `t₀` are
  irrelevant. -/
structure GeneralAssumption (g : H → ℝ) (t₀ : ℝ) (ε ε' : ℝ → ℝ) : Prop where
  convex : ConvexOn ℝ Set.univ g
  differentiable : Differentiable ℝ g
  differentiable_gradient : Differentiable ℝ (gradient g)
  lipschitz_gradient_on_bounded :
    ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (gradient g) (Metric.closedBall 0 R)
  argmin_nonempty : (argminSet g).Nonempty
  hasDerivWithinAt_eps : ∀ t ∈ Ici t₀, HasDerivWithinAt ε (ε' t) (Ici t₀) t
  continuousOn_eps_deriv : ContinuousOn ε' (Ici t₀)
  eps_nonneg : ∀ t ∈ Ici t₀, 0 ≤ ε t
  eps_antitoneOn : AntitoneOn ε (Ici t₀)
  eps_tendsto_zero : Tendsto ε atTop (𝓝 0)

/-- `x`, with velocity map `xd` (= `ẋ`) and acceleration map `xdd` (= `ẍ`), is a global
`C²`-solution on `[t₀, +∞)` of system (5):
`ẍ(t) + (α/t) ẋ(t) + β ∇²g(x(t)) ẋ(t) + ∇g(x(t)) + ε(t) x(t) = 0`, `x(t₀) = u₀`, `ẋ(t₀) = v₀`.
Derivatives are taken within `[t₀, +∞)` (one-sided at `t₀`), `ẍ` is continuous on `[t₀, +∞)`,
and `∇²g(x) v` is the Fréchet derivative of `∇g` at `x` applied to `v`. Values for `t < t₀`
are irrelevant. -/
def IsSolution (g : H → ℝ) (α β t₀ : ℝ) (ε : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) : Prop :=
  (∀ t ∈ Ici t₀,
      HasDerivWithinAt x (xd t) (Ici t₀) t ∧
      HasDerivWithinAt xd (xdd t) (Ici t₀) t ∧
      xdd t + (α / t) • xd t + β • (fderiv ℝ (gradient g) (x t)) (xd t)
        + gradient g (x t) + ε t • x t = 0) ∧
  ContinuousOn xdd (Ici t₀) ∧ x t₀ = u₀ ∧ xd t₀ = v₀

/-- `x⋆` is the element of minimum norm of `argmin g`: `x⋆ ∈ argmin g` and `‖x⋆‖ ≤ ‖z‖` for
every `z ∈ argmin g`. -/
def IsMinNormMinimizer (g : H → ℝ) (xstar : H) : Prop :=
  xstar ∈ argminSet g ∧ ∀ z ∈ argminSet g, ‖xstar‖ ≤ ‖z‖

end TikhonovHDD.Strong


