-- Prove2me | Definitions.Def_NAGFlow_Flow_Setting
-- name    : NAGFlow_Flow_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:12.972982+00:00
-- url     : https://prove2.me/theorems/44c24111-ec0c-416a-8ab8-e7ca803a2c46
-- title:
--   (2)–(3) p. 2, (54) p. 12, (56)–(58) p. 13 — the classes S¹_μ and S^{1,1}_{μ,L}, γ(t), solutions of (56) and of the NAG flow (57), and the Lyapunov function ℒ(t)
-- statement:
--   This file fixes the objects of Section 3.1 of Luo and Chen. Throughout, $V$ is a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
--
--   **Time derivatives on $[0,\infty)$.** For a curve $x:[0,\infty)\to V$, $x'(t)$ denotes its derivative relative to $[0,\infty)$; at $t=0$ this is the right derivative.
--
--   **The function classes (2)–(3).** A function $f:V\to\mathbb R$ belongs to $\mathcal S^1_\mu$ if it is continuously differentiable, with gradient $\nabla f$, and for some $\mu\ge0$
--   $$f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ \ge\ \frac{\mu}{2}\|x-y\|^2\qquad\forall\,x,y\in V.$$
--   It belongs to $\mathcal S^{1,1}_{\mu,L}$ if moreover $0<L<\infty$, $\mu\le L$, and $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$.
--
--   **The scaling factor.** For $\mu,\gamma_0\in\mathbb R$,
--   $$\gamma(t)=\mu+(\gamma_0-\mu)e^{-t},$$
--   the solution of (54) $\gamma'=\mu-\gamma$, $\gamma(0)=\gamma_0$.
--
--   **Solutions of (56).** Given a scaling function $\gamma$, a pair $(x,v)$ of curves is a classical solution of the system
--   $$x'=v-x,\qquad \gamma v'=\mu(x-v)-\nabla f(x),\qquad x(0)=x_0,\ v(0)=v_0,$$
--   if $x,v\in C^1([0,\infty);V)$ and both equations hold at every $t\ge0$.
--
--   **Solutions of the NAG flow (57).** With $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$, a curve $x$ solves (57) if $x\in C^2([0,\infty);V)$,
--   $$\gamma x''+(\mu+\gamma)x'+\nabla f(x)=0\qquad\text{for all }t\ge0,$$
--   and $x(0)=x_0$, $x'(0)=v_0-x_0$.
--
--   **The Lyapunov function (58).** For a point $x^*$, a scaling function $\gamma$ and curves $x,v$,
--   $$\mathcal L(t)=f(x(t))-f(x^*)+\frac{\gamma(t)}{2}\|v(t)-x^*\|^2 .$$
--   For the second-order form (57), which has no $v$, the paper's relation $x'=v-x$ gives $v=x+x'$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** The duality pairing $\langle\cdot,\cdot\rangle$ and the inner product $(\cdot,\cdot)$ of the paper are both the inner product of $V$, and the dual norm is the norm (Riesz identification). The gradient is an explicit map `gradf` with `HasGradientAt f (gradf x) x` everywhere and `gradf` continuous; Mathlib's `gradient f` is not used. Time derivatives are `dI x := derivWithin x (Ici 0)`. `derivWithin` returns $0$ where a curve is not differentiable, but every definition and statement that uses `dI` requires the curve to be $C^1$ or $C^2$ on $[0,\infty)$ (`ContDiffOn` on `Ici 0`), so `dI` is the genuine one-sided derivative there. The equation $\gamma v'=\mu(x-v)-\nabla f(x)$ is kept in the paper's unsolved form. Values of the curves at $t<0$ are irrelevant to every definition.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2)–(3) p. 2; (54) and the display after it, p. 12; (56), (57), (58), p. 13

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.Flow

open Set

/-- The one-sided time derivative on `[0, ∞)`: `dI x t = derivWithin x (Ici 0) t`. On the page every
time derivative `x′` of §3.1 is taken on `[0, ∞)` (solutions lie in `C^k([0, ∞); V)`), so at `t = 0` it
is the right derivative. `derivWithin` is `0` where `x` is not differentiable within `[0, ∞)`; every
statement using `dI` assumes `x` is `C¹` (or `C²`) on `[0, ∞)`, which rules that junk value out. -/
noncomputable def dI {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : ℝ → E) : ℝ → E :=
  derivWithin x (Ici (0 : ℝ))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The scaling factor `γ(t) = μ + (γ₀ − μ)e^{−t}`, p. 12: the solution, printed on the page, of
(54) `γ′ = μ − γ`, `γ(0) = γ₀`. -/
noncomputable def gammaFn (μ γ₀ : ℝ) : ℝ → ℝ := fun t => μ + (γ₀ - μ) * Real.exp (-t)

/-- A classical solution `(x, v) ∈ C¹([0, ∞); V) × C¹([0, ∞); V)` of the first-order system (56),
p. 13, with a general positive scaling function `γ` in place of the solution of (54):
`x′ = v − x`, `γ v′ = μ(x − v) − ∇f(x)` for every `t ≥ 0` (one-sided derivatives at `t = 0`),
`x(0) = x₀`, `v(0) = v₀`. The second equation is kept in the paper's (unsolved) form. -/
structure IsSys56 (f : V → ℝ) (gradf : V → V) (μ : ℝ) (γ : ℝ → ℝ) (x₀ v₀ : V)
    (x v : ℝ → V) : Prop where
  contDiff_x : ContDiffOn ℝ 1 x (Ici 0)
  contDiff_v : ContDiffOn ℝ 1 v (Ici 0)
  eq_x : ∀ t, 0 ≤ t → dI x t = v t - x t
  eq_v : ∀ t, 0 ≤ t → γ t • dI v t = μ • (x t - v t) - gradf (x t)
  init_x : x 0 = x₀
  init_v : v 0 = v₀

/-- A solution `x ∈ C²([0, ∞); V)` of the NAG flow (57), p. 13, with `γ(t) = μ + (γ₀ − μ)e^{−t}`:
`γ x″ + (μ + γ) x′ + ∇f(x) = 0` for every `t ≥ 0` (one-sided derivatives at `t = 0`),
`x(0) = x₀`, `x′(0) = v₀ − x₀`. -/
structure IsNAGSolution2 (f : V → ℝ) (gradf : V → V) (μ γ₀ : ℝ) (x₀ v₀ : V) (x : ℝ → V) :
    Prop where
  contDiff : ContDiffOn ℝ 2 x (Ici 0)
  ode : ∀ t, 0 ≤ t →
    gammaFn μ γ₀ t • dI (dI x) t + (μ + gammaFn μ γ₀ t) • dI x t + gradf (x t) = 0
  init_x : x 0 = x₀
  init_dx : dI x 0 = v₀ - x₀

/-- The Lyapunov function (58), p. 13: `ℒ(t) = f(x(t)) − f(x*) + γ(t)/2 ‖v(t) − x*‖²`. For the
second-order form (57), which has no `v`, the velocity variable is `v = x + x′` (from `x′ = v − x`
in (56)). -/
noncomputable def lyapFlow (f : V → ℝ) (xstar : V) (γ : ℝ → ℝ) (x v : ℝ → V) (t : ℝ) : ℝ :=
  f (x t) - f xstar + γ t / 2 * ‖v t - xstar‖ ^ 2

end NAGFlow.Flow


