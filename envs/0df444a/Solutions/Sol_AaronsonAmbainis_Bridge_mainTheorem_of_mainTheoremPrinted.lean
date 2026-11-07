-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mainTheorem_of_mainTheoremPrinted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:30:56.019496+00:00
-- url     : https://prove2.me/submissions/cb014f94-1275-4b51-9024-e63901468337

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_aa_hyps_force
import Theorems.Thm_AaronsonAmbainis_Bridge_sqrt_form_iff
import Theorems.Thm_AaronsonAmbainis_Level_inflR_nonneg


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheoremPrinted) : MainTheorem := by
  intro ι _ _ d f hbd hdeg hpos
  obtain ⟨hd, hne⟩ := aa_hyps_force hdeg hpos
  have : Nonempty ι := hne
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨j, hj⟩ := h ι d hd f hbd hdeg
  refine ⟨j, ?_⟩
  rw [← one_mul (Real.sqrt 15)] at hj
  exact (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hpos.le hD
    (Level.inflR_nonneg f j)).mp hj
end AaronsonAmbainis.Bridge
