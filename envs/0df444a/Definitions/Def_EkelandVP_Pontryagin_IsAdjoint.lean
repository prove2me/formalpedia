-- Prove2me | Definitions.Def_EkelandVP_Pontryagin_IsAdjoint
-- name    : EkelandVP_Pontryagin_IsAdjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:08:26.932229+00:00
-- url     : https://prove2.me/theorems/c58b2846-7676-4be1-a06b-2a16af8360e6
-- title:
--   (7.6) — adjoint equation dp/dt = −ᵗf_x′(x, u, t)·p, p(T) = g′(x(T)) along a control–trajectory pair
-- statement:
--   Let $f_x' : \mathbb R^n \times K \times \mathbb R \to \mathcal L(\mathbb R^n, \mathbb R^n)$ be a matrix-valued function (in the mission it is the Jacobian of the dynamics $f$ with respect to the state), let $g : \mathbb R^n \to \mathbb R$, let $T$ be a real number, let $u : \mathbb R \to K$ be a control and $x : \mathbb R \to \mathbb R^n$ a trajectory. A function $p : \mathbb R \to \mathbb R^n$ **solves the adjoint equation** along $(u, x)$,
--
--   $$
--   \frac{dp}{dt}(t) = -{}^t f_x'(x(t), u(t), t)\, p(t), \qquad p(T) = g'(x(T)), \qquad (7.6)
--   $$
--
--   if $p$ is continuous on $[0, T]$ and
--
--   $$
--   p(t) = \nabla g(x(T)) + \int_t^T {}^t f_x'(x(s), u(s), s)\, p(s)\, ds \qquad \text{for every } t \in [0, T].
--   $$
--
--   Here ${}^t A$ is the transpose of the matrix $A$ and $\nabla g(x(T))$ is the gradient of $g$ at $x(T)$, the vector representing $g'(x(T))$.
--
--   The adjoint vector $p$ is the multiplier of the Pontryagin maximum principle: Theorem 7.1 compares the values $\langle f(x(t), w, t), p(t)\rangle$ over the control values $w$.
--
--   **Formalization Note** The linear equation is written in integral form, integrated backwards from $T$: $p(t) = p(T) - \int_t^T \dot p = p(T) + \int_t^T {}^t f_x' p$. The transpose is Mathlib's Euclidean adjoint `ContinuousLinearMap.adjoint`, and $g'(x)$ is represented by `gradient g x`.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 349, Theorem 7.1, (7.6)

import Mathlib

namespace EkelandVP.Pontryagin

/-- Ekeland (1974), §7, p. 349, (7.6), in integral form: `p` solves the adjoint (linear) equation
`dp/dt = −ᵗf_x′(x(t), u(t), t) · p(t)`, `p(T) = g′(x(T))` along the pair `(u, x)`, i.e. `p` is
continuous on `[0, T]` and `p(t) = ∇g(x(T)) + ∫ₜᵀ ᵗf_x′(x(s), u(s), s) p(s) ds` for every
`t ∈ [0, T]`. Here `fx x u t` is the Jacobian `f_x′` of `f` in the state variable and its
transpose `ᵗf_x′` is the Euclidean adjoint `ContinuousLinearMap.adjoint`. -/
def IsAdjoint {n : ℕ} {K : Type*}
    (fx : EuclideanSpace ℝ (Fin n) → K → ℝ →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (T : ℝ) (u : ℝ → K)
    (x p : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContinuousOn p (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T, p t = gradient g (x T) +
      ∫ s in t..T, ContinuousLinearMap.adjoint (fx (x s) (u s) s) (p s)

end EkelandVP.Pontryagin


