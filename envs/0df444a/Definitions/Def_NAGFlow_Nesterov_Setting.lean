-- Prove2me | Definitions.Def_NAGFlow_Nesterov_Setting
-- name    : NAGFlow_Nesterov_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:29.614501+00:00
-- url     : https://prove2.me/theorems/814e19a7-ef00-4232-a0d5-76d856264fba
-- title:
--   (2)–(3) p. 2, (74) p. 16, Algorithm 1 p. 23, (96) p. 24 — the classes S¹_μ and S^{1,1}_{μ,L}, ℒ_k, runs of Nesterov's method and one step of (96)
-- statement:
--   This file fixes the objects of Section 6 of Luo and Chen. Throughout, $V$ is a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
--
--   **The function classes (2)–(3).** Let $f:V\to\mathbb R$ have gradient map $\nabla f:V\to V$. We say $f\in\mathcal S^1_\mu$ if $\mu\ge 0$, $f$ is continuously differentiable (it has gradient $\nabla f(x)$ at every $x$ and $\nabla f$ is continuous), and $f$ is $\mu$-convex:
--   $$f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ \ge\ \frac{\mu}{2}\|x-y\|^2\qquad\forall\,x,y\in V.$$
--   We say $f\in\mathcal S^{1,1}_{\mu,L}$ if moreover $0<L<\infty$, $\mu\le L$, and $\nabla f$ is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$.
--
--   **The Lyapunov function (74).** For a reference point $x^*$, parameters $\gamma_k$ and sequences $x_k,v_k$,
--   $$\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2 .$$
--
--   **Nesterov's accelerated gradient method (Algorithm 1).** Given $x_0,v_0\in V$ and $\gamma_0>0$, sequences $(\alpha_k,\gamma_k,x_k,y_k,v_k)$ form a run if for every $k=0,1,\dots$
--   1. $\alpha_k>0$ solves $L\alpha_k^2=(1-\alpha_k)\gamma_k+\mu\alpha_k$;
--   2. $\gamma_{k+1}=(1-\alpha_k)\gamma_k+\mu\alpha_k$;
--   3. $y_k=\dfrac{\alpha_k\gamma_kv_k+\gamma_{k+1}x_k}{\gamma_k+\mu\alpha_k}$;
--   4. $x_{k+1}$ is any point with $f(x_{k+1})\le f(y_k)-\frac{1}{2L}\|\nabla f(y_k)\|^2$;
--   5. $v_{k+1}=\dfrac{1}{\gamma_{k+1}}\big[(1-\alpha_k)\gamma_kv_k+\alpha_k(\mu y_k-\nabla f(y_k))\big]$.
--
--   **One step of the scheme (96).** Given $\alpha_k,\gamma_k,\gamma_{k+1}$ and $x_k,y_k,v_k,v_{k+1}$,
--   $$\frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_k,\qquad \frac{y_k-x_k}{\alpha_k}=\frac{\gamma_k}{\gamma_{k+1}}(v_k-y_k),\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_{k+1}}(y_k-v_k)-\frac{1}{\gamma_{k+1}}\nabla f(y_k).$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's duality pairing and dual norm $\|\cdot\|_*$ are identified with the inner product and the norm of $V$ (Riesz). The gradient is an explicit map `gradf` with `HasGradientAt f (gradf x) x` at every point, not Mathlib's `gradient`. Algorithm 1 writes $\alpha_k\in(0,1)$ in step 2; the run records only $\alpha_k>0$ (the choice of the positive root), because $\alpha_k\le 1$ is a conclusion of Theorem 6.1, and $\alpha_k=1$ does occur (when $\mu=L$). Step 5 is kept as an inequality, so any point with sufficient decrease is allowed, not only the gradient step (95). Inequality (4) is a consequence of the class and is not part of the definition.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2)–(3) p. 2; (74) p. 16; Algorithm 1 p. 23; (96) p. 24

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.Nesterov

/-- The discrete Lyapunov function (74), p. 16: `ℒ_k := f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`. -/
noncomputable def lyap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (xstar : V) (x v : ℕ → V) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  f (x k) - f xstar + γ k / 2 * ‖v k - xstar‖ ^ 2

/-- A run of Algorithm 1 (Nesterov accelerated gradient method), p. 23, with input `x₀, v₀` and
`γ₀ > 0`. For every `k`:
* step 2: `α_k > 0` solves `Lα_k² = (1 − α_k)γ_k + μα_k` (the page writes `α_k ∈ (0, 1)`; only the
  positivity is part of the run, `α_k ≤ 1` is a conclusion of Theorem 6.1);
* step 3: `γ_{k+1} = (1 − α_k)γ_k + μα_k`;
* step 4: `y_k = (α_kγ_kv_k + γ_{k+1}x_k)/(γ_k + μα_k)`;
* step 5: `x_{k+1}` is any point with `f(x_{k+1}) ≤ f(y_k) − (1/(2L))‖∇f(y_k)‖²`;
* step 6: `v_{k+1} = (1/γ_{k+1})[(1 − α_k)γ_kv_k + α_k(μy_k − ∇f(y_k))]`. -/
structure IsNAGRun {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (α γ : ℕ → ℝ) (x y v : ℕ → V) : Prop where
  gamma0_pos : 0 < γ 0
  alpha_pos : ∀ k, 0 < α k
  alpha_eq : ∀ k, L * α k ^ 2 = (1 - α k) * γ k + μ * α k
  gamma_eq : ∀ k, γ (k + 1) = (1 - α k) * γ k + μ * α k
  y_eq : ∀ k, y k = (1 / (γ k + μ * α k)) • ((α k * γ k) • v k + γ (k + 1) • x k)
  x_desc : ∀ k, f (x (k + 1)) ≤ f (y k) - 1 / (2 * L) * ‖gradf (y k)‖ ^ 2
  v_eq : ∀ k, v (k + 1) =
    (1 / γ (k + 1)) • (((1 - α k) * γ k) • v k + α k • (μ • y k - gradf (y k)))

/-- One step of the scheme (96), p. 24, in difference-quotient form: given `α_k`, `γ_k`, `γ_{k+1}`
and `x_k, y_k, v_k, v_{k+1}`,
`(γ_{k+1} − γ_k)/α_k = μ − γ_k`,
`(y_k − x_k)/α_k = (γ_k/γ_{k+1})(v_k − y_k)`,
`(v_{k+1} − v_k)/α_k = (μ/γ_{k+1})(y_k − v_k) − (1/γ_{k+1})∇f(y_k)`. -/
structure IsScheme96Step {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ αk γk γk1 : ℝ) (xk yk vk vk1 : V) : Prop where
  gamma_eq : (γk1 - γk) / αk = μ - γk
  y_eq : (1 / αk) • (yk - xk) = (γk / γk1) • (vk - yk)
  v_eq : (1 / αk) • (vk1 - vk) = (μ / γk1) • (yk - vk) - (1 / γk1) • gradf yk

end NAGFlow.Nesterov


