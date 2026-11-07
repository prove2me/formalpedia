-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.meanIncrementDegree_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:39:14.027689+00:00
-- url     : https://prove2.me/submissions/5a3a36e3-b502-4997-92b1-a4255c95b5d8

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_aa_hyps_force
import Theorems.Thm_AaronsonAmbainis_Level_cube_le_iff_mul_sqrt_le
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution :
    MeanIncrementDegreeBound ↔ MeanIncrementDegreePrinted := by
  constructor
  · intro h ι _ _ d f hbd hdeg hvar
    obtain ⟨hd, -⟩ := aa_hyps_force hdeg hvar
    have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hpi : 0 < Real.pi := Real.pi_pos
    obtain ⟨j, hj⟩ := h ι d f hbd hdeg hvar
    refine ⟨hd, j, ?_⟩
    have h' : variance f ^ 3 ≤ 36 * (Real.pi ^ 2 * (d : ℝ) ^ 2) ^ 4 * meanAbsIncr f j ^ 2 :=
      hj.trans (le_of_eq (by ring))
    rw [div_le_iff₀ (by positivity)]
    exact ((Level.cube_le_iff_mul_sqrt_le hvar.le (Level.meanAbsIncr_nonneg f j)).mp h').trans
      (le_of_eq (by ring))
  · intro h ι _ _ d f hbd hdeg hvar
    obtain ⟨hd, j, hj⟩ := h ι d f hbd hdeg hvar
    have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hpi : 0 < Real.pi := Real.pi_pos
    refine ⟨j, ?_⟩
    rw [div_le_iff₀ (by positivity)] at hj
    have h' : variance f * Real.sqrt (variance f)
        ≤ 6 * (Real.pi ^ 2 * (d : ℝ) ^ 2) ^ 2 * meanAbsIncr f j := hj.trans (le_of_eq (by ring))
    exact ((Level.cube_le_iff_mul_sqrt_le hvar.le (Level.meanAbsIncr_nonneg f j)).mpr h').trans
      (le_of_eq (by ring))
end AaronsonAmbainis.Bridge
