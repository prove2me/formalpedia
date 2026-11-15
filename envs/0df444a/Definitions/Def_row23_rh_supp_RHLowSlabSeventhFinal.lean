-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabSeventhFinal
-- name    : row23_rh_supp_RHLowSlabSeventhFinal
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:36:21.358439+00:00
-- url     : https://prove2.me/theorems/67242ab7-ad1a-4b54-a988-33cd001920fc
-- title:
--   Row 23 RH support: RHLowSlabSeventhFinal
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabSeventhPilot
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell01
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell02
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell03
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell04
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell05
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell06
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell07
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell08
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell09
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell10
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell11
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell12
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell13
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell14
import Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell15
import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_add
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open Arb4 Arb4.Q
namespace RHLowSlabSeventhPilot
theorem slab_clear : EdgeClearGlue.SlabClear (207 / 32 : ℝ) (13 / 2 : ℝ) := by
  have hc : ∀ j, j < slab.m → Arb4.cellOK slab j = true := by
    intro j hj
    have hm : slab.m = 16 := rfl
    rw [hm] at hj
    interval_cases j
    · exact cell0_checked
    · exact cell01_checked
    · exact cell02_checked
    · exact cell03_checked
    · exact cell04_checked
    · exact cell05_checked
    · exact cell06_checked
    · exact cell07_checked
    · exact cell08_checked
    · exact cell09_checked
    · exact cell10_checked
    · exact cell11_checked
    · exact cell12_checked
    · exact cell13_checked
    · exact cell14_checked
    · exact cell15_checked
  have hok : Arb4.slabOK slab = true := by
    simp only [Arb4.slabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    exact ⟨head_checked, hc⟩
  have h := Arb4.slabOK_sound slab hok
  have hlo : slab.lo.val = (207 / 32 : ℝ) := by
    change (Q.frac 207 32).val = _
    exact Q.cv_frac 207 32
  have hhi : slab.hi.val = (13 / 2 : ℝ) := by
    change (Q.add (Q.frac 207 32) (Q.frac 1 32)).val = _
    have hone : (Q.frac 1 32).val = (1 / 32 : ℝ) := by
      norm_num [Q.val, Q.frac]
    rw [Q.cv_add _ _ _ _ (Q.cv_frac 207 32) hone]
    norm_num
  rw [hlo, hhi] at h
  exact h
end RHLowSlabSeventhPilot
#print axioms RHLowSlabSeventhPilot.slab_clear


