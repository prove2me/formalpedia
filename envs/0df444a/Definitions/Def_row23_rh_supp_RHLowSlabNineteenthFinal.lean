-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabNineteenthFinal
-- name    : row23_rh_supp_RHLowSlabNineteenthFinal
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:18:17.722653+00:00
-- url     : https://prove2.me/theorems/784916d3-9a14-43f4-83f0-03d86488c9aa
-- title:
--   Row 23 RH support: RHLowSlabNineteenthFinal
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthPilot
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell01
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell02
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell03
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell04
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell05
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell06
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell07
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell08
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell09
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell10
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell11
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell12
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell13
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell14
import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell15
import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_add
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open Arb4 Arb4.Q
namespace RHLowSlabNineteenthPilot
theorem slab_clear : EdgeClearGlue.SlabClear (219 / 32 : ℝ) (220 / 32 : ℝ) := by
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
  have hlo : slab.lo.val = (219 / 32 : ℝ) := by
    change (Q.frac 219 32).val = _
    exact Q.cv_frac 219 32
  have hhi : slab.hi.val = (220 / 32 : ℝ) := by
    change (Q.add (Q.frac 219 32) (Q.frac 1 32)).val = _
    have hone : (Q.frac 1 32).val = (1 / 32 : ℝ) := by
      norm_num [Q.val, Q.frac]
    rw [Q.cv_add _ _ _ _ (Q.cv_frac 219 32) hone]
    norm_num
  rw [hlo, hhi] at h
  exact h
end RHLowSlabNineteenthPilot
#print axioms RHLowSlabNineteenthPilot.slab_clear


