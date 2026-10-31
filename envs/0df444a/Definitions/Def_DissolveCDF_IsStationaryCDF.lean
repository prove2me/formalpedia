-- Prove2me | Definitions.Def_DissolveCDF_IsStationaryCDF
-- name    : DissolveCDF_IsStationaryCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:59.21272+00:00
-- url     : https://prove2.me/theorems/f69e86e0-346f-4e17-8b6d-053d89588972
-- title:
--   Definition 2.6 — first-order stationary point of CDF
-- statement:
--   For a penalty parameter $\beta$, a point $x\in\mathbb R^n$ is a **first-order stationary point of CDF** if
--
--   $$
--   \nabla h(x)=0, \tag{2.6}
--   $$
--
--   where $h(x)=f(\mathcal A(x))+\frac\beta2\|c(x)\|^2$.
--
--   **Formalization Note** $\nabla h$ is Mathlib's `gradient`; under Assumptions 1.1 and 1.2 $h$ is differentiable, so this is the true gradient.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Definition 2.6, (2.6), p.6

import Mathlib
import Definitions.Def_DissolveCDF_cdf

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Definition 2.6 (p.6): `x ∈ ℝⁿ` is a **first-order stationary point of CDF** if
`∇h(x) = 0`, where `h` is the constraint dissolving function with penalty parameter `β`.

**Formalization Note** `∇h` is Mathlib's `gradient`; under Assumptions 1.1 and 1.2 `h` is
differentiable, so this is the true gradient. -/
def IsStationaryCDF {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient (cdf f c A β) x = 0

end DissolveCDF


