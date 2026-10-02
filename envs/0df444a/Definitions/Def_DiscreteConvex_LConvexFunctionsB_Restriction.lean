-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_Restriction
-- name    : DiscreteConvex_LConvexFunctionsB_Restriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:21:16.571994+00:00
-- url     : https://prove2.me/theorems/cb0e6861-f56a-4988-9428-d1f1e436a486
-- title:
--   Restriction
-- statement:
--   The restriction $g_U$ of $g$ to $U\subseteq V$, Eq. (6.40).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.40).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.40)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The restriction `g_U` of `g` to `U ⊆ V`, Eq. (6.40). -/
def Restriction (g : (V → ℤ) → WithTop ℝ) (U : Finset V) : (V → ℤ) → WithTop ℝ :=
  fun y => if (∀ v ∉ U, y v = 0) then g y else ⊤

end DiscreteConvex.LConvexFunctionsB


