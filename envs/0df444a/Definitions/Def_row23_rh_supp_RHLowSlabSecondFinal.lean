-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabSecondFinal
-- name    : row23_rh_supp_RHLowSlabSecondFinal
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:12:55.118768+00:00
-- url     : https://prove2.me/theorems/01d52d28-5514-4036-a965-750cf98eace9
-- title:
--   Row 23 RH support: RHLowSlabSecondFinal
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabSecondPilot
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell01
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell02
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell03
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell04
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell05
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell06
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell07
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell08
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell09
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell10
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell11
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell12
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell13
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell14
import Definitions.Def_row23_rh_supp_RHLowSlabSecondCell15
import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_add
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open Arb4 Arb4.Q
namespace RHLowSlabSecondPilot
theorem slab_clear : EdgeClearGlue.SlabClear (101 / 16 : ℝ) (203 / 32 : ℝ) := by
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
  have hlo : slab.lo.val = (101 / 16 : ℝ) := by
    change (Q.frac 101 16).val = _
    exact Q.cv_frac 101 16
  have hhi : slab.hi.val = (203 / 32 : ℝ) := by
    change (Q.add (Q.frac 101 16) (Q.frac 1 32)).val = _
    have hone : (Q.frac 1 32).val = (1 / 32 : ℝ) := by
      norm_num [Q.val, Q.frac]
    rw [Q.cv_add _ _ _ _ (Q.cv_frac 101 16) hone]
    norm_num
  rw [hlo, hhi] at h
  exact h
end RHLowSlabSecondPilot
#print axioms RHLowSlabSecondPilot.slab_clear


