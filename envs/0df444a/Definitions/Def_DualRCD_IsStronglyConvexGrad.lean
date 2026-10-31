-- Prove2me | Definitions.Def_DualRCD_IsStronglyConvexGrad
-- name    : DualRCD_IsStronglyConvexGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:32.534059+00:00
-- url     : https://prove2.me/theorems/b1a440e3-5ce3-47db-bc93-617c1cd555f8
-- title:
--   $g$ is differentiable and $\sigma$-strongly convex (first-order form)
-- statement:
--   A function $g:\mathbb R^n\to\mathbb R$ is $\sigma$-strongly convex if it is differentiable and
--   $$
--   \frac\sigma2\|y-x\|^2\le g(y)-g(x)-\langle\nabla g(x),y-x\rangle\qquad\forall x,y\in\mathbb R^n .
--   $$
--   This is the left inequality of the pair the paper uses to define smooth strongly convex functions. After rescaling, the paper takes $\sigma=1$ in all its theorems.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §2, p.4 (left inequality), p.5 (scaling)

import Mathlib

open scoped RealInnerProductSpace

namespace DualRCD

/-- `g : ℝⁿ → ℝ` is differentiable and `σ`-strongly convex, in the first-order form of the left
inequality on Necoara & Fercoq, arXiv:1911.06014v1, §2, p.4:
`σ/2 ‖y − x‖² ≤ g(y) − g(x) − ⟨∇g(x), y − x⟩` for all `x, y`.

**Formalization Note.** `gradient` is Mathlib's Fréchet gradient; `Differentiable ℝ g` is part of the
predicate, because Lean's `gradient` is `0` at a point of non-differentiability. -/
def IsStronglyConvexGrad {n : ℕ} (σ : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Differentiable ℝ g ∧
    ∀ x y, σ / 2 * ‖y - x‖ ^ 2 ≤ g y - g x - ⟪gradient g x, y - x⟫

end DualRCD


