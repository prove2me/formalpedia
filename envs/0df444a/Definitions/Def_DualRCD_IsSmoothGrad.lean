-- Prove2me | Definitions.Def_DualRCD_IsSmoothGrad
-- name    : DualRCD_IsSmoothGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:30.969897+00:00
-- url     : https://prove2.me/theorems/f810b8bf-b6eb-4a71-90b5-1f8ef3f1e26f
-- title:
--   $g$ is differentiable and $L$-smooth (first-order form)
-- statement:
--   A function $g:\mathbb R^n\to\mathbb R$ is $L$-smooth, in the form the paper uses, if it is differentiable and
--   $$
--   g(y)-g(x)-\langle\nabla g(x),y-x\rangle\le\frac L2\|y-x\|^2\qquad\forall x,y\in\mathbb R^n .
--   $$
--   This is the right inequality of the pair on p.4 of the paper.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §2, p.4 (right inequality)

import Mathlib

open scoped RealInnerProductSpace

namespace DualRCD

/-- `g : ℝⁿ → ℝ` is differentiable and `L`-smooth, in the first-order form of the right inequality
on Necoara & Fercoq, arXiv:1911.06014v1, §2, p.4:
`g(y) − g(x) − ⟨∇g(x), y − x⟩ ≤ L/2 ‖y − x‖²` for all `x, y`.

**Formalization Note.** Together with `IsStronglyConvexGrad` this is the paper's two-sided inequality
for the pair `(σ, L)`. As on p.4, it is the form of smoothness the paper works with. -/
def IsSmoothGrad {n : ℕ} (L : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Differentiable ℝ g ∧
    ∀ x y, g y - g x - ⟪gradient g x, y - x⟫ ≤ L / 2 * ‖y - x‖ ^ 2

end DualRCD


