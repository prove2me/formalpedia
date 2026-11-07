-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.influence_printed_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:59.511472+00:00
-- url     : https://prove2.me/submissions/c74919af-d0f0-4d0a-a359-a581c4929b39

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Average_pow_le_iff_sqrt_mul_le


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {V K L I : ℝ} (hV : 0 < V) (hK : 0 < K) (hL0 : 0 ≤ L)
    (hLK : L ≤ K) (hI : 0 ≤ I) (h : 3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2) :
    0 < L ∧ Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / (L * K ^ 2) ≤ I ∧
      Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / K ^ 3 ≤ I := by
  have hL : 0 < L := by
    rcases hL0.eq_or_lt with h0 | hpos
    · exfalso
      rw [← h0] at h
      have h5 : 0 < V ^ 5 := pow_pos hV 5
      have e : 3125 * (0 : ℝ) ^ 2 * K ^ 4 * I ^ 2 = 0 := by ring
      rw [e] at h
      linarith
    · exact hpos
  have h1 := (Average.pow_le_iff_sqrt_mul_le hV.le hL.le hI).mp h
  have hq : Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / (L * K ^ 2) ≤ I := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  refine ⟨hL, hq, le_trans ?_ hq⟩
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc L * K ^ 2 ≤ K * K ^ 2 := mul_le_mul_of_nonneg_right hLK (sq_nonneg K)
    _ = K ^ 3 := by ring
end AaronsonAmbainis.Bridge
