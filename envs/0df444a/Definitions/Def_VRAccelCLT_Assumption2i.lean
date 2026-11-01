-- Prove2me | Definitions.Def_VRAccelCLT_Assumption2i
-- name    : VRAccelCLT_Assumption2i
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:11.585486+00:00
-- url     : https://prove2.me/theorems/2a9e59bb-29f5-4ece-aa32-04549ea1cfbb
-- title:
--   Assumption 2 (i): Hessian $H$ at $x^*$ with quadratic remainder (29)
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ have gradient $\nabla f$, let $x^*\in\mathbb R^m$ and $H\in\mathbb R^{m\times m}$. **Assumption 2 (i)** holds with constant $R_D>0$ if $\nabla f$ is differentiable at $x^*$ with Hessian $H$ and
--
--   $$
--   \nabla f(x)=H(x-x^*)+D(x)(x-x^*)\quad\text{with}\quad \|D(x)\|\le R_D\|x-x^*\| \tag{29}
--   $$
--
--   for some matrices $D(x)$. Equivalently,
--
--   $$
--   \|\nabla f(x)-H(x-x^*)\|\ \le\ R_D\,\|x-x^*\|^2\qquad\text{for all }x\in\mathbb R^m .
--   $$
--
--   This controls the linearization error of the gradient around the optimum, which drives the asymptotic analysis of Theorems 1–4.
--
--   **Formalization Note** The definition uses the second (equivalent) form: given $D$, the bound follows from $\|D(x)\|\le R_D\|x-x^*\|$; conversely $D(x)=(\nabla f(x)-H(x-x^*))(x-x^*)^T/\|x-x^*\|^2$ (and $D(x^*)=0$) satisfies (29) in the matrix 2-norm. The bound makes $H$ the derivative of $\nabla f$ at $x^*$. No symmetry of $H$ is assumed.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Assumption 2 (i), eq. (29), p.14

import Mathlib

namespace VRAccelCLT

/-- **Assumption 2 (i)**: the gradient is differentiable at `x∗` with Hessian `H`, with a
quadratic remainder bound (29). Lei, Shanbhag, arXiv:2006.07769v3, Assumption 2, p.14:
"(i) ∇f : Rm → Rm is differentiable at x∗ with Hessian matrix H ∈ Rm×m, and
∇f(x) = H(x − x∗) + D(x)(x − x∗) with ∥D(x)∥ ≤ RD∥x − x∗∥ for some RD > 0. (29)"

`Assumption2i f xstar H RD` states `R_D > 0` and `‖∇f(x) − H(x − x∗)‖ ≤ R_D ‖x − x∗‖²` for all `x`.

**Formalization Note.** This is equivalent to (29) with the matrix 2-norm: given `D`,
`‖∇f(x) − H(x−x∗)‖ ≤ ‖D(x)‖ ‖x−x∗‖ ≤ R_D‖x−x∗‖²`; conversely
`D(x) = (∇f(x) − H(x−x∗))(x−x∗)ᵀ / ‖x−x∗‖²` (and `D(x∗) = 0`) satisfies (29). The bound also makes
`H` the derivative of `∇f` at `x∗`, so "differentiable at `x∗` with Hessian `H`" is implied. `H`
acts on vectors through `Matrix.toEuclideanLin`. No symmetry of `H` is assumed. -/
def Assumption2i {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (xstar : EuclideanSpace ℝ (Fin m))
    (H : Matrix (Fin m) (Fin m) ℝ) (RD : ℝ) : Prop :=
  0 < RD ∧ ∀ x : EuclideanSpace ℝ (Fin m),
    ‖gradient f x - Matrix.toEuclideanLin H (x - xstar)‖ ≤ RD * ‖x - xstar‖ ^ 2

end VRAccelCLT


