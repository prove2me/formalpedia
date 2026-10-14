-- Prove2me | solution 1 for Apery.potential_ineq
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T00:40:36.464979+00:00
-- url     : https://prove2.me/submissions/521e4745-92fa-4e92-b6f3-08e50faa198a

/-
# The potential inequality for all `t > 0`: the two case bounds

`t ≤ 2` is the Table-2 certificate `Apery.potential_ineq_le_two`; `t ≥ 2` is the
tail bound `Apery.potential_ineq_tail` of `Apery/PotentialIneq.lean` (platform
definition module `Definitions.Def_Zeta5_SourcePotentialIneq`). Faithful to
`Apery/PotentialIneqFinal.lean` of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy
import Definitions.Def_Zeta5_SourcePotentialIneq
import Theorems.Thm_Apery_potential_ineq_le_two

open Finset Filter Topology Set MeasureTheory

theorem solution (t : ℝ) (ht : 0 < t) :
    2 * Apery.Uρ t - Apery.Vfield t ≤ Apery.M0 := by
  rcases le_or_gt t 2 with h | h
  · exact Apery.potential_ineq_le_two t ht h
  · exact Apery.potential_ineq_tail h.le
