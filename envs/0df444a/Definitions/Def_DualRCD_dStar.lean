-- Prove2me | Definitions.Def_DualRCD_dStar
-- name    : DualRCD_dStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:21.922978+00:00
-- url     : https://prove2.me/theorems/329a0d91-d1f1-4014-a3ab-65cdbf6d5a4e
-- title:
--   Dual optimal value $d^*$
-- statement:
--   The dual optimal value is
--   $$
--   d^*=\min_{y\in\mathbb R^{mn}}d(y).
--   $$
--
--   **Formalization Note.** It is defined as an infimum in the extended reals. Under Slater's condition it is finite and attained.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, display (10), p.7

import Mathlib
import Definitions.Def_DualRCD_dualFn

namespace DualRCD

/-- The optimal value `d* = min_y d(y)` of the dual problem (10) (Necoara & Fercoq,
arXiv:1911.06014v1, p.7), as an infimum in `EReal`. Under Slater's condition it is finite and
attained (`DualRCD.strong_duality_slater`). -/
noncomputable def dStar {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) : EReal :=
  ⨅ y : DualSpace n m, dualFn g X y

end DualRCD


