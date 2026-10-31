-- Prove2me | Definitions.Def_OneStepProx_scaledProx
-- name    : OneStepProx_scaledProx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:31.828628+00:00
-- url     : https://prove2.me/theorems/a062ffd1-10a7-478d-bf1e-17fbfc61bb7f
-- title:
--   The scaled proximal operator $\operatorname{prox}^C_h(x)$, as a set of minimizers
-- statement:
--   Let $C$ be a real $d\times d$ matrix, positive definite in all uses, and let $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$ be given by its effective domain $D$ and its finite values on $D$. The **scaled proximal operator** of $h$ at $x\in\mathbb R^d$ is
--
--   $$
--   \operatorname{prox}^C_h(x)=\operatorname*{argmin}_{w\in\mathbb R^d}\Bigl\{h(w)+\tfrac12\|w-x\|_C^2\Bigr\},
--   $$
--
--   understood as the set of all minimizers: the points $p\in D$ with $h(p)+\frac12\|p-x\|_C^2\le h(w)+\frac12\|w-x\|_C^2$ for all $w\in D$.
--
--   Taking $C=\lambda^{-1}I$ recovers the usual proximal operator with step length $\lambda$. One step of scaled proximal gradient descent on $g+h$ from $x$ is a point of $\operatorname{prox}^C_h(x-C^{-1}\nabla g(x))$.
--
--   **Formalization Note** The set may be empty, because a function that is not lower semicontinuous need not attain its infimum. The paper assumes existence where it needs it, and so do the statements of this mission. For positive definite $C$ and proper convex $h$ the set has at most one point.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, §1.2, p.5, definition of the scaled proximal operator

import Mathlib
import Definitions.Def_OneStepProx_scaledSqNorm

namespace OneStepProx

/-- The scaled proximal operator
`prox^C_h(x) := argmin_{w ∈ ℝ^d} { h(w) + ½‖w − x‖²_C }`
(Bassett & Deride, arXiv:2004.14521v3, §1.2, p.5), as the **set** of minimizers.

**Formalization Note.** The function `h : ℝ^d → ℝ ∪ {∞}` is encoded by its effective domain `D`
and its finite values `h` on `D` (see `IsProperConvex`), so for a nonempty `D` a minimizer lies in
`D` and it suffices to compare with the points of `D`. The set may be empty: without lower
semicontinuity a minimizer need not exist, which is why the paper assumes the existence of its
one-step estimator (2.2). -/
def scaledProx {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {p | p ∈ D ∧ ∀ w ∈ D, h p + 1 / 2 * scaledSqNorm C (p - x) ≤ h w + 1 / 2 * scaledSqNorm C (w - x)}

end OneStepProx


