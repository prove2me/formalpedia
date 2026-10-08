-- Prove2me | Definitions.Def_TikhonovHDD_Weak_Setting
-- name    : TikhonovHDD_Weak_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:21.974039+00:00
-- url     : https://prove2.me/theorems/08bf500f-5cda-448f-afe5-6c8fdab1330f
-- title:
--   System (5), the General assumption, conditions (a)/(b) and weak convergence of a trajectory (pp. 2, 11)
-- statement:
--   This file fixes the model studied by Boţ, Csetnek and László.
--
--   Let $\mathcal H$ be a real Hilbert space and $g:\mathcal H\to\mathbb R$.
--
--   1. $\operatorname{argmin} g=\{x\in\mathcal H: g(x)\le g(y)\ \text{for all } y\}$, and $\min g=\inf_{y\in\mathcal H}g(y)$ (the infimum of the range of $g$, which is the minimal value whenever $\operatorname{argmin} g\neq\emptyset$).
--   2. **General assumption on $g$:** $g$ is convex, twice Fréchet differentiable ($g$ and $\nabla g$ are differentiable), $\nabla g$ is Lipschitz continuous on every ball $\bar B(0,R)$, and $\operatorname{argmin} g\neq\emptyset$.
--   3. **General assumption on $\epsilon$:** given $t_0$, a function $\epsilon$ with derivative map $\dot\epsilon$ such that on $[t_0,+\infty)$, $\epsilon$ is $C^1$ (one-sided derivative at $t_0$, $\dot\epsilon$ continuous), $\epsilon\ge 0$, $\epsilon$ is nonincreasing, and $\epsilon(t)\to0$ as $t\to+\infty$.
--   4. **Global $C^2$-solution of (5):** maps $x,\dot x,\ddot x:\mathbb R\to\mathcal H$ such that for every $t\ge t_0$, $\dot x(t)$ is the derivative of $x$ at $t$ and $\ddot x(t)$ that of $\dot x$ (within $[t_0,+\infty)$), $\ddot x$ is continuous on $[t_0,+\infty)$, and
--   $$\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,$$
--   with $x(t_0)=u_0$, $\dot x(t_0)=v_0$. Here $\nabla^2 g(x)v$ is the derivative of $\nabla g$ at $x$ in direction $v$.
--   5. **Condition (a):** there exist $a>1$ and $t_1\ge t_0$ with $\dot\epsilon(t)\le-\frac{a\beta}{2}\epsilon^2(t)$ for all $t\ge t_1$. **Condition (b):** there exist $a>0$ and $t_1\ge t_0$ with $\epsilon(t)\le\frac{a}{t}$ for all $t\ge t_1$.
--   6. **Weak convergence of a trajectory:** $x(t)\rightharpoonup p$ as $t\to+\infty$ means $\langle x(t),v\rangle\to\langle p,v\rangle$ for every $v\in\mathcal H$.
--
--   These are the objects in which every statement of Section 3 of the paper is phrased.
--
--   **Formalization Note** Values of $x$, $\epsilon$ before $t_0$ are irrelevant; derivatives at $t_0$ are one-sided. The positivity $t_0>0$, $\beta\ge0$ and the bound on $\alpha$ are hypotheses of each theorem, not part of these definitions.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 2, (5) and General assumption; p. 11, conditions (a), (b) of Theorem 3.3; p. 15, Theorem 3.5 (weak convergence)

import Mathlib

open Filter Topology Set

namespace TikhonovHDD.Weak

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The set of minimizers of `g : H → ℝ`: `argmin g = {x | g x ≤ g y for every y}`. -/
def argmin (g : H → ℝ) : Set H := {x | ∀ y, g x ≤ g y}

/-- The minimal value `min g`, encoded as the infimum of the range of `g`. Whenever
`argmin g` is nonempty (as in the General assumption) this infimum is attained, and
`minVal g = g x̂` for every `x̂ ∈ argmin g`. -/
noncomputable def minVal (g : H → ℝ) : ℝ := sInf (Set.range g)

/-- The first half of the General assumption (p. 2): `g` is convex, twice Fréchet differentiable
(`g` and its gradient `∇g` are differentiable), `∇g` is Lipschitz continuous on bounded sets
(on every closed ball centred at the origin), and `argmin g ≠ ∅`. -/
def GenAssumptionG (g : H → ℝ) : Prop :=
  ConvexOn ℝ Set.univ g ∧ Differentiable ℝ g ∧ Differentiable ℝ (gradient g) ∧
    (∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (gradient g) (Metric.closedBall 0 R)) ∧
    (argmin g).Nonempty

/-- The second half of the General assumption (p. 2): on `[t₀, +∞)` the Tikhonov parameter
`ε` is of class `C¹` with derivative `ε'` (one-sided at `t₀`), nonnegative, nonincreasing,
and `ε t → 0` as `t → +∞`. Values of `ε`, `ε'` before `t₀` are irrelevant. -/
def GenAssumptionEps (t₀ : ℝ) (ε ε' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ici t₀, HasDerivWithinAt ε (ε' t) (Ici t₀) t) ∧ ContinuousOn ε' (Ici t₀) ∧
    (∀ t ∈ Ici t₀, 0 ≤ ε t) ∧ AntitoneOn ε (Ici t₀) ∧ Tendsto ε atTop (𝓝 0)

/-- `x` is a global `C²`-solution of system (5) on `[t₀, +∞)`, with velocity `xd` and
acceleration `xdd` (one-sided derivatives within `[t₀, +∞)`, `xdd` continuous there):
for every `t ≥ t₀`,
`ẍ(t) + (α/t) ẋ(t) + β ∇²g(x(t)) ẋ(t) + ∇g(x(t)) + ε(t) x(t) = 0`,
together with `x t₀ = u₀` and `ẋ t₀ = v₀`. Values for `t < t₀` are irrelevant. -/
def IsSolution (g : H → ℝ) (ε : ℝ → ℝ) (α β t₀ : ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) : Prop :=
  (∀ t ∈ Ici t₀, HasDerivWithinAt x (xd t) (Ici t₀) t) ∧
    (∀ t ∈ Ici t₀, HasDerivWithinAt xd (xdd t) (Ici t₀) t) ∧
    ContinuousOn xdd (Ici t₀) ∧
    (∀ t ∈ Ici t₀, xdd t + (α / t) • xd t + β • fderiv ℝ (gradient g) (x t) (xd t) +
        gradient g (x t) + ε t • x t = 0) ∧
    x t₀ = u₀ ∧ xd t₀ = v₀

/-- Condition (a) of Theorems 3.3–3.5: there exist `a > 1` and `t₁ ≥ t₀` such that
`ε̇(t) ≤ -(aβ/2) ε(t)²` for every `t ≥ t₁`. -/
def CondA (β t₀ : ℝ) (ε ε' : ℝ → ℝ) : Prop :=
  ∃ a : ℝ, 1 < a ∧ ∃ t₁ : ℝ, t₀ ≤ t₁ ∧ ∀ t, t₁ ≤ t → ε' t ≤ -(a * β / 2) * ε t ^ 2

/-- Condition (b) of Theorems 3.3–3.5: there exist `a > 0` and `t₁ ≥ t₀` such that
`ε(t) ≤ a / t` for every `t ≥ t₁`. -/
def CondB (t₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ t₁ : ℝ, t₀ ≤ t₁ ∧ ∀ t, t₁ ≤ t → ε t ≤ a / t

/-- Weak convergence of a curve `x : ℝ → H` to `p` as `t → +∞`:
`⟪x t, v⟫ → ⟪p, v⟫` for every `v ∈ H`. -/
def WeakTendstoAtTop (x : ℝ → H) (p : H) : Prop :=
  ∀ v : H, Tendsto (fun t => inner ℝ (x t) v) atTop (𝓝 (inner ℝ p v))

end TikhonovHDD.Weak


