-- Prove2me | Definitions.Def_NAGFlow_PredCorr_Setting
-- name    : NAGFlow_PredCorr_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:34:30.512012+00:00
-- url     : https://prove2.me/theorems/c9c4cd5a-c1c8-4c70-af33-960a877fd12a
-- title:
--   (2)–(3) p. 2, (73)–(74) p. 16, (80) p. 19, (83)–(84) p. 20 — the classes S¹_μ and S^{1,1}_{μ,L}, the γ recursion, ℒ_k, ℒ̂_k, the Gauss–Seidel step and the predictor–corrector scheme
-- statement:
--   This file fixes the objects of Sections 4 and 5 of Luo and Chen. Throughout, $V$ is a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
--
--   **The function classes (2)–(3).** Let $f:V\to\mathbb R$ have gradient map $\nabla f:V\to V$. We say $f\in\mathcal S^1_\mu$ if $\mu\ge 0$, $f$ is continuously differentiable (it has gradient $\nabla f(x)$ at every $x$ and $\nabla f$ is continuous), and $f$ is $\mu$-convex:
--   $$f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ \ge\ \frac{\mu}{2}\|x-y\|^2\qquad\forall\,x,y\in V.$$
--   We say $f\in\mathcal S^{1,1}_{\mu,L}$ if moreover $0<L<\infty$, $\mu\le L$, and $\nabla f$ is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$.
--
--   **The Lyapunov function (74) and (84).** For a reference point $x^*$, parameters $\gamma_k$ and sequences $x_k,v_k,y_k$,
--   $$\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2,\qquad \widehat{\mathcal L}_k=f(y_k)-f(x^*)+\frac{\gamma_{k+1}}{2}\|v_{k+1}-x^*\|^2 .$$
--   Both are instances of the one-point expression $f(x)-f(x^*)+\frac{\gamma}{2}\|v-x^*\|^2$.
--
--   **The parameter equation (73).** $\gamma_0>0$, every step size $\alpha_k>0$, and
--   $$\frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_{k+1}\qquad(k\in\mathbb N).$$
--
--   **One Gauss–Seidel step (80).** Given $(x_k,v_k)$, $\alpha_k$, $\gamma_k$, the pair $(x_{k+1},v_{k+1})$ satisfies
--   $$\frac{x_{k+1}-x_k}{\alpha_k}=v_k-x_{k+1},\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(x_{k+1}-v_{k+1})-\frac{1}{\gamma_k}\nabla f(x_{k+1}).$$
--
--   **The predictor–corrector scheme (83).** Sequences $(x_k,y_k,v_k)$ form a run if for every $k$
--   $$\frac{y_k-x_k}{\alpha_k}=v_k-y_k,\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(y_k-v_{k+1})-\frac{1}{\gamma_k}\nabla f(y_k),\qquad \frac{x_{k+1}-x_k}{\alpha_k}=v_{k+1}-x_{k+1}.$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's duality pairing and dual norm $\|\cdot\|_*$ are identified with the inner product and the norm of $V$ (Riesz). The gradient is an explicit map `gradf` with `HasGradientAt f (gradf x) x` at every point, not Mathlib's `gradient`. Every update is kept in the paper's difference-quotient form, as an equation on given sequences; the implicit equations are not solved. The step size and $\gamma$ positivity are carried in `IsGammaRun`; the schemes themselves do not restrict $\alpha_k$, $\gamma_k$, and the theorems state where positivity is needed. Inequality (4), $f(x)-f(y)-\langle\nabla f(y),x-y\rangle\le\frac L2\|x-y\|^2$, is a consequence of the class and is not part of the definition.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2)–(3) p. 2; (73)–(74) p. 16; (80) p. 19; (83)–(84) p. 20

import Mathlib

namespace NAGFlow.PredCorr

/-- `f ∈ S¹_μ` (Luo & Chen, (2), p. 2, with Ω = V): `f` is continuously differentiable, with gradient
map `gradf` (`∇f`), and μ-convex: `f x − f y − ⟪∇f(y), x − y⟫ ≥ (μ/2)‖x − y‖²` for all `x, y`,
with `μ ≥ 0`. -/
structure IsS1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ : ℝ) : Prop where
  mu_nonneg : 0 ≤ μ
  hasGrad : ∀ x, HasGradientAt f (gradf x) x
  grad_cont : Continuous gradf
  mu_convex : ∀ x y, f x - f y - inner ℝ (gradf y) (x - y) ≥ μ / 2 * ‖x - y‖ ^ 2

/-- `f ∈ S^{1,1}_{μ,L}` (Luo & Chen, (2)–(3), p. 2, with Ω = V and `0 ≤ μ ≤ L < ∞`): `f ∈ S¹_μ` and
`∇f` is `L`-Lipschitz, `‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖`, with `0 < L`. -/
structure IsS11 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) : Prop extends IsS1 f gradf μ where
  L_pos : 0 < L
  mu_le_L : μ ≤ L
  grad_lip : ∀ x y, ‖gradf x - gradf y‖ ≤ L * ‖x - y‖

/-- The Lyapunov expression `f(x) − f(x*) + (γ/2)‖v − x*‖²` at a single point `(x, v, γ)`;
(74), p. 16, and (84), p. 20, are instances of it. -/
noncomputable def lyapPt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (xstar x v : V) (γ : ℝ) : ℝ :=
  f x - f xstar + γ / 2 * ‖v - xstar‖ ^ 2

/-- The discrete Lyapunov function (74), p. 16: `ℒ_k := f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`. -/
noncomputable def lyap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (xstar : V) (x v : ℕ → V) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  lyapPt f xstar (x k) (v k) (γ k)

/-- The intermediate Lyapunov value (84), p. 20: `ℒ̂_k := f(y_k) − f(x*) + (γ_{k+1}/2)‖v_{k+1} − x*‖²`. -/
noncomputable def lyapHat {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (xstar : V) (y v : ℕ → V) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  lyapPt f xstar (y k) (v (k + 1)) (γ (k + 1))

/-- The parameter sequence of (73), p. 16: `γ₀ > 0`, every step size `α_k > 0`, and
`(γ_{k+1} − γ_k)/α_k = μ − γ_{k+1}` for every `k` (difference-quotient form). -/
structure IsGammaRun (μ : ℝ) (α γ : ℕ → ℝ) : Prop where
  gamma0_pos : 0 < γ 0
  alpha_pos : ∀ k, 0 < α k
  gamma_eq : ∀ k, (γ (k + 1) - γ k) / α k = μ - γ (k + 1)

/-- One step of the Gauss–Seidel splitting (80), p. 19, in difference-quotient form: from
`(x_k, v_k)` with step `α_k` and parameter `γ_k`, the pair `(x', v') = (x_{k+1}, v_{k+1})` satisfies
`(x_{k+1} − x_k)/α_k = v_k − x_{k+1}` and
`(v_{k+1} − v_k)/α_k = (μ/γ_k)(x_{k+1} − v_{k+1}) − (1/γ_k)∇f(x_{k+1})`. Both equations are implicit
and are kept as equations. -/
structure IsGSStep {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ αk γk : ℝ) (xk vk x' v' : V) : Prop where
  x_eq : (1 / αk) • (x' - xk) = vk - x'
  v_eq : (1 / αk) • (v' - vk) = (μ / γk) • (x' - v') - (1 / γk) • gradf x'

/-- A run of the predictor–corrector scheme (83), p. 20, in difference-quotient form: for every `k`,
`(y_k − x_k)/α_k = v_k − y_k`,
`(v_{k+1} − v_k)/α_k = (μ/γ_k)(y_k − v_{k+1}) − (1/γ_k)∇f(y_k)`, and
`(x_{k+1} − x_k)/α_k = v_{k+1} − x_{k+1}`. The parameters `α, γ` are those of (73) (`IsGammaRun`). -/
structure IsPCRun {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ : ℝ) (α γ : ℕ → ℝ) (x y v : ℕ → V) : Prop where
  y_eq : ∀ k, (1 / α k) • (y k - x k) = v k - y k
  v_eq : ∀ k, (1 / α k) • (v (k + 1) - v k) =
    (μ / γ k) • (y k - v (k + 1)) - (1 / γ k) • gradf (y k)
  x_eq : ∀ k, (1 / α k) • (x (k + 1) - x k) = v (k + 1) - x (k + 1)

end NAGFlow.PredCorr


