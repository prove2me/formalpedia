-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsRationalPolytope
-- name    : CombOpt_ChvatalRank_IsRationalPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:34.571451+00:00
-- url     : https://prove2.me/theorems/ede61ab2-7bfa-4885-affa-7ecc3650a1fb
-- title:
--   Rational polytope
-- statement:
--   A **rational polytope** is a polytope that is a rational polyhedron.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.4, pp. 218–219 (PDF 226–227), and Theorems 6.31, 6.32, 6.35

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsPolytope
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolyhedron

open Matrix

namespace CombOpt.ChvatalRank

/-- **Rational polytope.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.4, pp. 218–219 (PDF 226–227): a polytope that is a rational
polyhedron; the phrase is used without further definition in Theorems 6.31, 6.32, 6.35. -/
def IsRationalPolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  IsRationalPolyhedron P ∧ IsPolytope P

end CombOpt.ChvatalRank


