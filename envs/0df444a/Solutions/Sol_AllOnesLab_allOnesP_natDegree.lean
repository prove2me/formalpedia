-- Prove2me | solution 1 for AllOnesLab.allOnesP_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:47.939387+00:00
-- url     : https://prove2.me/submissions/42f3a6b0-6cf2-4005-83ed-9571ca0af33a

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_P_natDegree
import Theorems.Thm_AllOnesLab_allOnes_natDegree
import Theorems.Thm_AllOnesLab_allOnesP_eq_comp

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) : (allOnesP n).natDegree = 2 * n := by
  rw [allOnesP_eq_comp, natDegree_comp, allOnes_natDegree, P_natDegree, Nat.mul_comm]
end AllOnesLab
