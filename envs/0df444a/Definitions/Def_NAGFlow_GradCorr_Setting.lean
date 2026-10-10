-- Prove2me | Definitions.Def_NAGFlow_GradCorr_Setting
-- name    : NAGFlow_GradCorr_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:59.791871+00:00
-- url     : https://prove2.me/theorems/fd0b6abd-7c59-40aa-9e47-b0c2cdf1dc1d
-- title:
--   (2)–(3) p. 2, (73)–(74) p. 16, (80) p. 19, (84) p. 20, (91) p. 22 — S¹_μ, S^{1,1}_{μ,L}, the γ recursion, ℒ_k, ℒ̂_k, the Gauss–Seidel step and the gradient-corrected scheme
-- statement:
--   This file fixes the objects of Section 5 of Luo and Chen used by the gradient-corrected scheme of §5.3. Throughout, $V$ is a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
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
--   **The gradient-corrected scheme (91).** Sequences $(x_k,y_k,v_k)$ form a run if for every $k$
--   $$\frac{y_k-x_k}{\alpha_k}=v_k-y_k,\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(y_k-v_{k+1})-\frac{1}{\gamma_k}\nabla f(y_k),\qquad x_{k+1}-y_k=-\frac{1}{L}\nabla f(y_k).$$
--   The first two lines are one Gauss–Seidel step (80) with $x_{k+1}$ replaced by $y_k$; the third is one gradient descent step with step size $1/L$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's duality pairing and dual norm $\|\cdot\|_*$ are identified with the inner product and the norm of $V$ (Riesz). The gradient is an explicit map `gradf` with `HasGradientAt f (gradf x) x` at every point, not Mathlib's `gradient`. Every update is kept in the paper's form, as an equation on given sequences; the implicit equations are not solved. Positivity of $\gamma_0$ and of the step sizes is carried in `IsGammaRun`; the schemes themselves do not restrict $\alpha_k$, $\gamma_k$, $L$, and the theorems state where positivity is needed. Inequality (4), $f(x)-f(y)-\langle\nabla f(y),x-y\rangle\le\frac L2\|x-y\|^2$, is a consequence of the class and is not part of the definition.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2)–(3) p. 2; (73)–(74) p. 16; (80) p. 19; (84) p. 20; (91) p. 22

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.GradCorr

/-- A run of the corrected scheme (91), p. 22, in difference-quotient form: for every `k`,
`(y_k − x_k)/α_k = v_k − y_k`,
`(v_{k+1} − v_k)/α_k = (μ/γ_k)(y_k − v_{k+1}) − (1/γ_k)∇f(y_k)`, and the gradient correction step
`x_{k+1} − y_k = −(1/L)∇f(y_k)`. The parameters `α, γ` are those of (73) (`IsGammaRun`). -/
structure IsGCRun {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ L : ℝ) (α γ : ℕ → ℝ) (x y v : ℕ → V) : Prop where
  y_eq : ∀ k, (1 / α k) • (y k - x k) = v k - y k
  v_eq : ∀ k, (1 / α k) • (v (k + 1) - v k) =
    (μ / γ k) • (y k - v (k + 1)) - (1 / γ k) • gradf (y k)
  x_eq : ∀ k, x (k + 1) - y k = -(1 / L) • gradf (y k)

end NAGFlow.GradCorr


