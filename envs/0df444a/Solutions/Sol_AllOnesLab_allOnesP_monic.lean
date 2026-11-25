-- Prove2me | solution 1 for AllOnesLab.allOnesP_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:13.509911+00:00
-- url     : https://prove2.me/submissions/74e40fee-0cdb-418f-b996-0f7cc9c36c7f

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_P_monic
import Theorems.Thm_AllOnesLab_P_natDegree
import Theorems.Thm_AllOnesLab_allOnes_monic
import Theorems.Thm_AllOnesLab_allOnesP_eq_comp
section
open Polynomial
namespace AllOnesLab
private lemma P_natDegree_ne_zero : P.natDegree ≠ 0 := by
  rw [P_natDegree]; omega
end AllOnesLab
end

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) : (allOnesP n).Monic := by
  rw [allOnesP_eq_comp]
  exact (allOnes_monic n).comp P_monic P_natDegree_ne_zero
end AllOnesLab
