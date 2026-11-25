-- Prove2me | solution 1 for AllOnesLab.allOnes_coeff_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:59.146064+00:00
-- url     : https://prove2.me/submissions/44a8639b-42d5-4e59-8841-80fce81ace48

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_allOnes_coeff_eq

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n i : ℕ) (hi : n < i) : (allOnes n).coeff i = 0 := by
  rw [allOnes_coeff_eq, if_neg (by omega : ¬ i ≤ n)]
end AllOnesLab
