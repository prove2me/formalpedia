-- Prove2me | Definitions.Def_DualRCD_HasQuadraticGrowthOn
-- name    : DualRCD_HasQuadraticGrowthOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:37.518542+00:00
-- url     : https://prove2.me/theorems/7f4e0013-f4d7-421e-9ace-0173fb242d45
-- title:
--   Quadratic growth (21) on the sublevel set of $y^0$
-- statement:
--   The dual has quadratic growth with constant $\sigma$ on the sublevel set of $y^0$ if
--   $$
--   d(y)-d^*\ge\frac\sigma2\operatorname{dist}^2(y,Y^*)\qquad\forall y:\ d(y)\le d(y^0).
--   $$
--
--   **Formalization Note.** The paper's display (21) prints $\operatorname{dist}^2(y,Y^*)^2$. Definition 3 (7), the end of the proof of Theorem 3 and the use of (21) on p.18 all have $\operatorname{dist}^2$, which is what is stated.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, display (21), p.16

import Mathlib
import Definitions.Def_DualRCD_dualGap
import Definitions.Def_DualRCD_Ystar

namespace DualRCD

/-- The quadratic growth condition (21) of Necoara & Fercoq, arXiv:1911.06014v1, p.16:
`d(y) − d* ≥ σ/2 · dist²(y, Y*)` for all `y` with `d(y) ≤ d(y⁰)`.

**Formalization Note.** The display prints `dist²(y, Y*)²`. Definition 3 (7), the end of the proof of
Theorem 3 and the use of (21) on p.18 all have `dist²`, which is what is stated. The distance is
Mathlib's `Metric.infDist` in the Euclidean norm of `DualSpace`; it is `0` for empty `Y*`, which
Slater's condition excludes (`DualRCD.strong_duality_slater`). -/
def HasQuadraticGrowthOn {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) (y0 : DualSpace n m) (σ : ℝ) : Prop :=
  ∀ y : DualSpace n m, dualFn g X y ≤ dualFn g X y0 →
    σ / 2 * Metric.infDist y (Ystar g X) ^ 2 ≤ dualGap g X y

end DualRCD


