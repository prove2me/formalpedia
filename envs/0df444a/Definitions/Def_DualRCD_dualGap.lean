-- Prove2me | Definitions.Def_DualRCD_dualGap
-- name    : DualRCD_dualGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:25.603718+00:00
-- url     : https://prove2.me/theorems/9bf7038f-3639-475a-97c2-78bf306337ac
-- title:
--   Dual gap $d(y)-d^*$
-- statement:
--   The dual gap of a point $y$ is the real number $d(y)-d^*$.
--
--   **Formalization Note.** It is the conversion to a real number of the extended-real difference. It is used only on the sublevel set of a point with $d(y^0)<+\infty$, where both terms are finite under Slater's condition, so the conversion loses nothing there.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, Theorem 4, p.16

import Mathlib
import Definitions.Def_DualRCD_dStar

namespace DualRCD

/-- The dual gap `d(y) − d*` as a real number (Necoara & Fercoq, arXiv:1911.06014v1, Theorem 4, p.16).

**Formalization Note.** `EReal.toReal` sends `±∞` to `0`. The gap is only used at points of the
sublevel set `{d ≤ d(y⁰)}` with `d(y⁰) < +∞`, and under Slater's condition `d*` is finite and
`d > −∞`, so there it is the true difference. -/
noncomputable def dualGap {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) (y : DualSpace n m) : ℝ :=
  (dualFn g X y - dStar g X).toReal

end DualRCD


