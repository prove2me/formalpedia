-- Prove2me | Definitions.Def_RollingProbeQN_Convex_hess
-- name    : RollingProbeQN_Convex_hess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:56.695054+00:00
-- url     : https://prove2.me/theorems/4744a928-69bd-4d47-91e1-0ffab368eb3c
-- title:
--   The Hessian $H(x)=\nabla^2 f(x)$
-- statement:
--   For a function $f:\mathbb R^d\to\mathbb R$ and a point $x\in\mathbb R^d$, the **Hessian** $H(x)=\nabla^2 f(x)$ is the derivative at $x$ of the gradient map $x\mapsto\nabla f(x)$, a linear map of $\mathbb R^d$ into itself. Its matrix entry $(i,j)$ is $\langle e_i,H(x)e_j\rangle$.
--
--   All curvature statements of the mission (bounds $0\preceq H(x)\preceq L_1I$, the Lipschitz bound on $H$, the sparsity pattern) are about this map.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; the Hessian is `fderiv ℝ (gradient f) x`, which for $f$ of class $C^2$ is the symmetric Hessian.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, §2, p. 6

import Mathlib

namespace RollingProbeQN.Convex

/-- **The Hessian `H(x) = ∇²f(x)`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §2, p. 6: "The Hessian is `H(x) = ∇²f(x)`".

`hess f x` is the derivative of the gradient map of `f` at `x`, a continuous linear map of
`ℝ^d`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. For `f` of class `C²` this is the
symmetric Hessian; its matrix entry `(i, j)` is `⟪e_i, hess f x e_j⟫`. -/
noncomputable def hess {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  fderiv ℝ (gradient f) x

end RollingProbeQN.Convex


