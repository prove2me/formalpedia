-- Prove2me | solution 1 for ApproxPolySatCH.Main.mrv_in_ch
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:44.657623+00:00
-- url     : https://prove2.me/submissions/b2674216-d7c9-404c-a274-b1464af7c340
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ApproxPolySatCH_Main_coefficient_zero_in_ch
import Theorems.Thm_ApproxPolySatCH_Main_mrv_of_coefficient_zero
import Theorems.Thm_ApproxPolySatCH_Main_mrvFinite_of_coefficientZeroFinite

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution : InCH (MRV .rational) ∧ InCH MRVFinite := by
  exact ⟨ApproxPolySatCH.Main.mrv_of_coefficient_zero .rational
      ApproxPolySatCH.Main.coefficient_zero_in_ch.1,
    ApproxPolySatCH.Main.mrvFinite_of_coefficientZeroFinite
      ApproxPolySatCH.Main.coefficient_zero_in_ch.2⟩
