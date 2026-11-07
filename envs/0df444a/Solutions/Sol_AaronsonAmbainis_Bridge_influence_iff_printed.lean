-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.influence_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:54.798786+00:00
-- url     : https://prove2.me/submissions/15a0ec7d-7a18-4ca8-8c91-d8aa1e8aa593

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_rows_iff_printed
import Theorems.Thm_AaronsonAmbainis_Bridge_influence_printed_arith
import Theorems.Thm_AaronsonAmbainis_Level_cost_pos
import Theorems.Thm_AaronsonAmbainis_Level_inflR_nonneg
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg
import Theorems.Thm_AaronsonAmbainis_Level_sum_meanAbsIncr_le_cost


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : InfluenceBound ↔ InfluencePrinted := by
  constructor
  · intro h ι _ _ f K hrow hvar
    obtain ⟨a, ha0, ha1, ha2⟩ := (rows_iff_printed f K).mpr hrow
    obtain ⟨j, hj⟩ := h ι f K a ha0 ha1 ha2 hvar
    have hLK : ∑ k, meanAbsIncr f k ≤ K := Level.sum_meanAbsIncr_le_cost ha1 ha2
    obtain ⟨hL, h1, h2⟩ := influence_printed_arith hvar (Level.cost_pos ha0 ha1 ha2 hvar)
      (Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k) hLK (Level.inflR_nonneg f j) hj
    exact ⟨hL, hLK, j, hj, h1, h2⟩
  · intro h ι _ _ f K a ha0 ha1 ha2 hvar
    obtain ⟨-, -, j, hj, -, -⟩ := h ι f K ((rows_iff_printed f K).mp ⟨a, ha0, ha1, ha2⟩) hvar
    exact ⟨j, hj⟩
end AaronsonAmbainis.Bridge
