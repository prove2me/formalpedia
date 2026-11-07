-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mainTheoremPrinted_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:30:41.509527+00:00
-- url     : https://prove2.me/submissions/907b9f14-6e58-4889-8dc5-403e6c330bc5

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_sqrt_form_iff
import Theorems.Thm_AaronsonAmbainis_Level_inflR_nonneg
import Theorems.Thm_AaronsonAmbainis_Level_variance_nonneg


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) : MainTheoremPrinted := by
  intro ι _ _ hne d hd f hbd hdeg
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rcases (Level.variance_nonneg f).lt_or_eq with hpos | hzero
  · obtain ⟨j, hj⟩ := h ι d f hbd hdeg hpos
    have h1 := (sqrt_form_iff (c₁ := 1) (c₂ := 500) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hpos.le hD (Level.inflR_nonneg f j)).mpr hj
    rw [one_mul] at h1
    exact ⟨j, h1⟩
  · obtain ⟨j⟩ := hne
    refine ⟨j, ?_⟩
    rw [← hzero, zero_pow two_ne_zero, zero_mul, mul_zero, zero_div]
    exact Level.inflR_nonneg f j
end AaronsonAmbainis.Bridge
