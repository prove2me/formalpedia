-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabTenthFinal
-- name    : row23_rh_supp_RHLowSlabTenthFinal
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:47:21.569992+00:00
-- url     : https://prove2.me/theorems/453f4fd1-6672-40aa-a535-ac27f560a263
-- title:
--   Row 23 RH support: RHLowSlabTenthFinal
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabTenthPilot
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell01
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell02
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell03
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell04
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell05
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell06
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell07
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell08
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell09
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell10
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell11
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell12
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell13
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell14
import Definitions.Def_row23_rh_supp_RHLowSlabTenthCell15
import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_add
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open Arb4 Arb4.Q
namespace RHLowSlabTenthPilot
theorem slab_clear : EdgeClearGlue.SlabClear (210 / 32 : ℝ) (211 / 32 : ℝ) := by
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
  have hlo : slab.lo.val = (210 / 32 : ℝ) := by
    change (Q.frac 210 32).val = _
    exact Q.cv_frac 210 32
  have hhi : slab.hi.val = (211 / 32 : ℝ) := by
    change (Q.add (Q.frac 210 32) (Q.frac 1 32)).val = _
    have hone : (Q.frac 1 32).val = (1 / 32 : ℝ) := by
      norm_num [Q.val, Q.frac]
    rw [Q.cv_add _ _ _ _ (Q.cv_frac 210 32) hone]
    norm_num
  rw [hlo, hhi] at h
  exact h
end RHLowSlabTenthPilot
#print axioms RHLowSlabTenthPilot.slab_clear


