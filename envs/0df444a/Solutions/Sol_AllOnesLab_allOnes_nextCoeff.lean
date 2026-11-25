-- Prove2me | solution 1 for AllOnesLab.allOnes_nextCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:46.272224+00:00
-- url     : https://prove2.me/submissions/7d1a4ed8-dd4c-410b-8e72-448163865dd8

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_allOnes_coeff
import Theorems.Thm_AllOnesLab_allOnes_natDegree

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) : (allOnes n).nextCoeff = 1 := by
  rw [nextCoeff_of_natDegree_pos (by rw [allOnes_natDegree]; omega), allOnes_natDegree]
  exact allOnes_coeff n (n - 1) (by omega)
end AllOnesLab
