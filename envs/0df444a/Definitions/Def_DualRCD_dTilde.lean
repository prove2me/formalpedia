-- Prove2me | Definitions.Def_DualRCD_dTilde
-- name    : DualRCD_dTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:35.390981+00:00
-- url     : https://prove2.me/theorems/fb1b1675-6efe-408a-a506-07b9f1b51c44
-- title:
--   Smooth part of the dual, $\tilde d(y)=g^*(-\sum_iy_i)$
-- statement:
--   The smooth part of the dual objective is
--   $$
--   \tilde d(y)=g^*\Big(-\sum_{i=1}^my_i\Big),
--   $$
--   where $g^*(z)=\sup_x\langle x,z\rangle-g(x)$ is the Fenchel conjugate of $g$. For strongly convex $g$ it is finite everywhere.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, display (10), p.7

import Mathlib
import Definitions.Def_DualRCD_DualSpace
import Definitions.Def_fenchelConjugate

namespace DualRCD

/-- The smooth part of the dual, `d̃(y) = g*(−Σᵢ yᵢ)` (Necoara & Fercoq, arXiv:1911.06014v1,
display (10), p.7), with `g*` the Fenchel conjugate of p.4. -/
noncomputable def dTilde {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (y : DualSpace n m) : EReal :=
  ConvexOptimization.fenchelConjugate g (-∑ j, y j)

end DualRCD


