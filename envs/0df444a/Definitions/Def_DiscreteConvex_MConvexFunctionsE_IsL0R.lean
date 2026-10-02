-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsL0R
-- name    : DiscreteConvex_MConvexFunctionsE_IsL0R
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:40.586341+00:00
-- url     : https://prove2.me/theorems/0463ce95-0af2-43e5-8d00-1c691453e86f
-- title:
--   IsL0R
-- statement:
--   The class $L_0[\mathbb R]$: polyhedra that are the admissible-potential set of some triangle-inequality distance function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167-168, class $L_0[\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167-168, class $L_0[\\mathbb R]$

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_AdmissiblePotentials

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `L0[R]`: polyhedra that are the admissible-potential set of some
triangle-inequality distance function. -/
def IsL0R (P : Set (V → ℝ)) : Prop :=
  ∃ γ : V → V → WithTop ℝ, TriangleInequality γ ∧ P = AdmissiblePotentials γ

end DiscreteConvex.MConvexFunctionsE


