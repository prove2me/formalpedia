-- Prove2me | Definitions.Def_ErrBoundCplx_ISTA_ForwardBackward
-- name    : ErrBoundCplx_ISTA_ForwardBackward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:55.226443+00:00
-- url     : https://prove2.me/theorems/fc3ff379-071d-4745-8263-1e0a09bbc405
-- title:
--   Example 2, (17): the forward-backward splitting method
-- statement:
--   Let $H$ be a real Hilbert space, $g : H \to (-\infty, +\infty]$, $h : H \to \mathbb R$ differentiable with gradient $\nabla h$, and $(\lambda_k)_{k \in \mathbb N}$ positive stepsizes. Starting from an arbitrary $x_0 \in H$, the **forward-backward splitting method** (proximal gradient method) generates $(x_k)_{k\in\mathbb N}$ by
--   $$x_{k+1} \in \operatorname{argmin}\Big\{ g(z) + \langle \nabla h(x_k), z - x_k\rangle + \frac{1}{2\lambda_k}\|z - x_k\|^2 : z \in H \Big\} \qquad (k \ge 0).$$
--   Equivalently $x_{k+1} = \operatorname{prox}_{\lambda_k g}(x_k - \lambda_k \nabla h(x_k))$ (18). For $h = 0$ it is the proximal point algorithm, for $g = 0$ the explicit gradient method.
--
--   The predicate says that every $x_{k+1}$ is a minimizer of the displayed model function; it is the algorithm of Proposition 13.
--
--   **Formalization Note** The minimization is written as an inequality against every $z \in H$, with values in `EReal`. $\nabla h$ is Mathlib's `gradient`. The page writes "(17) for $k \ge 1$"; since $x_1$ is built from $x_0$, the recursion is stated for every $k \ge 0$.
-- source:
--   arXiv:1510.08234v3, Example 2, pp. 14–15, (17), (18)

import Mathlib
open scoped InnerProductSpace

namespace ErrBoundCplx.ISTA

/-- Example 2, (17), p. 15: the forward-backward splitting method for `g + h`, with
`g : H → (−∞, +∞]` and `h : H → ℝ` differentiable, stepsizes `λ_k`, started at an arbitrary
`x₀ ∈ H`: for every `k ≥ 0`, `x_{k+1}` is a minimizer over `z ∈ H` of
`g(z) + ⟨∇h(x_k), z − x_k⟩ + (1/(2λ_k)) ‖z − x_k‖²`.
The comparison is in `EReal`; `∇h` is Mathlib's `gradient` (Riesz representative of the
Fréchet derivative). -/
def IsForwardBackwardSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → EReal) (h : H → ℝ) (lam : ℕ → ℝ) (x : ℕ → H) : Prop :=
  ∀ k : ℕ, ∀ z : H,
    g (x (k + 1)) + ((⟪gradient h (x k), x (k + 1) - x k⟫_ℝ
        + 1 / (2 * lam k) * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) ≤
      g z + ((⟪gradient h (x k), z - x k⟫_ℝ + 1 / (2 * lam k) * ‖z - x k‖ ^ 2 : ℝ) : EReal)

end ErrBoundCplx.ISTA


