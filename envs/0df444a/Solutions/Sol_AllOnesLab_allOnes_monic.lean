-- Prove2me | solution 1 for AllOnesLab.allOnes_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:43.367272+00:00
-- url     : https://prove2.me/submissions/3f5aa2ce-3e23-4bb5-80b2-98e9d6af87bf

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_allOnes_coeff
import Theorems.Thm_AllOnesLab_allOnes_natDegree

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) : (allOnes n).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (allOnes_natDegree n).le (allOnes_coeff n n le_rfl)
end AllOnesLab
