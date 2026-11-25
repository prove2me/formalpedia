-- Prove2me | solution 1 for AllOnesLab.allOnes_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:56.560826+00:00
-- url     : https://prove2.me/submissions/7c937026-c31c-40f2-ab42-a4fe8f982408

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_allOnes_coeff_eq

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n i : ℕ) (hi : i ≤ n) : (allOnes n).coeff i = 1 := by
  rw [allOnes_coeff_eq, if_pos hi]
end AllOnesLab
