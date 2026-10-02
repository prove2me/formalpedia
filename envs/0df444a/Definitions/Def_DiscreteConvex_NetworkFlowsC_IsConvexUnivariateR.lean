-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_IsConvexUnivariateR
-- name    : DiscreteConvex_NetworkFlowsC_IsConvexUnivariateR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:11.372221+00:00
-- url     : https://prove2.me/theorems/f2fcc6ec-9551-4054-9e95-e824d92cbc3e
-- title:
--   IsConvexUnivariateR
-- statement:
--   A univariate real function is convex (a proxy for membership in $C[R\to R]$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, notation C[R→R].)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, notation C[R→R]

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate real function is convex (a proxy for membership in `C[R→R]`). -/
def IsConvexUnivariateR (g : ℝ → WithTop ℝ) : Prop :=
  (∃ x, g x ≠ ⊤) ∧ ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    g (t * x + (1 - t) * y) ≤ (t : WithTop ℝ) * g x + ((1 - t : ℝ) : WithTop ℝ) * g y

-- ===== Network transformation apparatus (§9.6), integer domain =====

end DiscreteConvex.NetworkFlowsC


