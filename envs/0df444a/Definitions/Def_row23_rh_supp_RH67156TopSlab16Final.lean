-- Prove2me | Definitions.Def_row23_rh_supp_RH67156TopSlab16Final
-- name    : row23_rh_supp_RH67156TopSlab16Final
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:33:53.323674+00:00
-- url     : https://prove2.me/theorems/f1aede70-cd1b-4911-b373-36fb55e57975
-- title:
--   Row 23 RH support: RH67156TopSlab16Final
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_Arb4_Q_cv_nat
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_add
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell00
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell01
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell02
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell03
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell04
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell05
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell06
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell07
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell08
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell09
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell10
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell11
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell12
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell13
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell14
import Definitions.Def_row23_rh_supp_RH67156Slab16Cell15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open Arb4 Arb4.Q
namespace RH67156TopSlab16R016

/-- A zero-free slab begins at the upper edge of the new band. -/
theorem top_slab_clear :
    EdgeClearGlue.SlabClear (67156 : ℝ) ((67156 : ℝ) + 25 / 8192) := by
  have hcells : ∀ j, j < slab.m → Arb4.cellOK slab j = true := by
    intro j hj
    have hm : slab.m = 16 := rfl
    rw [hm] at hj
    interval_cases j
    · exact cell00_checked
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
    exact ⟨head_checked, hcells⟩
  have h := Arb4.slabOK_sound slab hok
  have hlo : slab.lo.val = (67156 : ℝ) := by
    change (Q.ofNat 67156).val = (67156 : ℝ)
    exact Q.cv_nat 67156
  have hhi : slab.hi.val = (67156 : ℝ) + 25 / 8192 := by
    change (Q.add (Q.ofNat 67156) (Q.frac 25 8192)).val = _
    exact Q.cv_add _ _ _ _ (Q.cv_nat 67156) (Q.cv_frac 25 8192)
  rw [hlo, hhi] at h
  exact h

end RH67156TopSlab16R016
#print axioms RH67156TopSlab16R016.top_slab_clear


