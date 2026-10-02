-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_RestrictionR
-- name    : DiscreteConvex_LConvexFunctionsC_RestrictionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:23.663539+00:00
-- url     : https://prove2.me/theorems/7bdb3455-5e5b-4472-a164-04bc338fad96
-- title:
--   RestrictionR
-- statement:
--   The restriction $g_U$ of $g$ to $U\subseteq V$ for real-domain $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.40), real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.40), real-variable analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The restriction `g_U` of `g` to `U ⊆ V` for real-domain `g`. -/
noncomputable def RestrictionR (g : (V → ℝ) → WithTop ℝ) (U : Finset V) : (V → ℝ) → WithTop ℝ :=
  fun y => if (∀ v ∉ U, y v = 0) then g y else ⊤

end DiscreteConvex.LConvexFunctionsC


