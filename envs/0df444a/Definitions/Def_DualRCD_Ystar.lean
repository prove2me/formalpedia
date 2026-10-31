-- Prove2me | Definitions.Def_DualRCD_Ystar
-- name    : DualRCD_Ystar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:27.007677+00:00
-- url     : https://prove2.me/theorems/1534b5fe-122e-46d9-9e21-95b3fd0d59df
-- title:
--   Dual optimal set $Y^*$
-- statement:
--   The dual optimal set is $Y^*=\arg\min_yd(y)\subseteq\mathbb R^{mn}$, the set of $y$ with $d(y)\le d(y')$ for every $y'$. The rate of RCD is expressed in terms of the distance to this set.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §3.1, p.7

import Mathlib
import Definitions.Def_DualRCD_dualFn

namespace DualRCD

/-- The dual optimal set `Y* = arg min_y d(y) ⊆ ℝ^{mn}` (Necoara & Fercoq, arXiv:1911.06014v1, §3.1,
p.7). -/
def Ystar {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) : Set (DualSpace n m) :=
  {y | ∀ y', dualFn g X y ≤ dualFn g X y'}

end DualRCD


