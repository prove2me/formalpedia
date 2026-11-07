-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.meanIncrement_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:53.092204+00:00
-- url     : https://prove2.me/submissions/e59ed8e3-8411-44d5-83cb-ca72a09d64d5

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_rows_iff_printed
import Theorems.Thm_AaronsonAmbainis_Level_cost_pos
import Theorems.Thm_AaronsonAmbainis_Level_cube_le_iff_mul_sqrt_le
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : MeanIncrementBound ↔ MeanIncrementPrinted := by
  constructor
  · intro h ι _ _ f K hrow hvar
    obtain ⟨a, ha0, ha1, ha2⟩ := (rows_iff_printed f K).mpr hrow
    have hK : 0 < K := Level.cost_pos ha0 ha1 ha2 hvar
    obtain ⟨j, hj⟩ := h ι f K a ha0 ha1 ha2 hvar
    refine ⟨hK, j, hj, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    exact ((Level.cube_le_iff_mul_sqrt_le hvar.le (Level.meanAbsIncr_nonneg f j)).mp hj).trans
      (le_of_eq (by ring))
  · intro h ι _ _ f K a ha0 ha1 ha2 hvar
    obtain ⟨-, j, hj, -⟩ := h ι f K ((rows_iff_printed f K).mp ⟨a, ha0, ha1, ha2⟩) hvar
    exact ⟨j, hj⟩
end AaronsonAmbainis.Bridge
