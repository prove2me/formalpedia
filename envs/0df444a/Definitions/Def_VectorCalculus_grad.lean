-- Prove2me | Definitions.Def_VectorCalculus_grad
-- name    : VectorCalculus_grad
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T00:01:58.375187+00:00
-- url     : https://prove2.me/theorems/18b21d8c-c7b0-4450-8c94-60e74a88c451
-- title:
--   Partial derivatives and the gradient $\nabla\phi$ on $\mathbb{R}^n$
-- statement:
--   The $i$-th partial derivative of a scalar field $\phi:\mathbb R^n\to\mathbb R$ at a point $y$ is obtained by differentiating with respect to the $i$-th variable while keeping all others fixed,
--
--   $$\frac{\partial\phi}{\partial x^i}(y) = \lim_{\epsilon\to 0}\frac{\phi(y + \epsilon\,e_i) - \phi(y)}{\epsilon},$$
--
--   and the gradient $\nabla\phi$ is the vector field whose $i$-th component is $\partial\phi/\partial x^i$.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.1 (pp. 19–20), equations (1.14)–(1.16)

import Mathlib

namespace VectorCalculus

/-- The `i`-th partial derivative of a scalar field `φ` on `ℝⁿ` at the point `y`:
the ordinary derivative, at `s = yᵢ`, of the one-variable function obtained from `φ`
by replacing its `i`-th argument by `s` and keeping all other arguments fixed. -/
noncomputable def partialDeriv {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (i : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  deriv (fun s : ℝ => φ (Function.update y i s)) (y i)

/-- The gradient `∇φ` of a scalar field `φ` on `ℝⁿ`: the vector field whose `i`-th
component is the `i`-th partial derivative of `φ`. -/
noncomputable def grad {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => partialDeriv φ i y

end VectorCalculus


