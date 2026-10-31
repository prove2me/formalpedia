-- Prove2me | Definitions.Def_DualRCD_IsConjMaximizer
-- name    : DualRCD_IsConjMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:31.961414+00:00
-- url     : https://prove2.me/theorems/5ef42e5d-0f9c-49ae-94ba-1bb851d9ab52
-- title:
--   $x=\nabla g^*(z)$: the arg max of $\langle z,\cdot\rangle-g$
-- statement:
--   For $z\in\mathbb R^n$, the point $x$ is a maximizer of $\langle z,\cdot\rangle-g$ if
--   $$
--   \langle z,x'\rangle-g(x')\le\langle z,x\rangle-g(x)\qquad\forall x'\in\mathbb R^n .
--   $$
--   By the formula on p.15 of the paper, this $x$ is $\nabla g^*(z)$. It is the primal point attached to a dual point: $x(y)$ is the maximizer for $z=-\sum_iy_i$.
--
--   **Formalization Note.** The predicate form avoids junk values. For strongly convex $g$ exactly one such $x$ exists. The paper's "arg min" in the definition of $x(y)$ on pp.14 and 18 is a typo for this arg max.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, p.15; x(y) on p.14

import Mathlib

open scoped RealInnerProductSpace

namespace DualRCD

/-- `x` is the arg max of `⟨z, ·⟩ − g`, i.e. `x = ∇g*(z)` by the formula
`∇g*(−Σⱼ yⱼ) = arg max_{x∈ℝⁿ} ⟨−Σⱼ yⱼ, x⟩ − g(x)` of Necoara & Fercoq, arXiv:1911.06014v1, p.15.

**Formalization Note.** A predicate, so no junk value arises. For a strongly convex `g` exactly one
such `x` exists for every `z`, and it is the gradient of the conjugate
(`DualRCD.conjugate_gradient_lipschitz`). The paper's `x(y) = arg min_x …` on pp.14 and 18 is this
arg max (typo). -/
def IsConjMaximizer {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (z x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x', ⟪z, x'⟫ - g x' ≤ ⟪z, x⟫ - g x

end DualRCD


