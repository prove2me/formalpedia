-- Prove2me | solution 1 for AllOnesLab.allOnes_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:07.069841+00:00
-- url     : https://prove2.me/submissions/1207bb66-2db7-44a5-b797-0192d648bd3b

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_allOnes_coeff
import Theorems.Thm_AllOnesLab_allOnes_coeff_of_lt

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) : (allOnes n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN => allOnes_coeff_of_lt n N hN
  · rw [allOnes_coeff n n le_rfl]
    exact one_ne_zero
end AllOnesLab
