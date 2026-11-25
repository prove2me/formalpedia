-- Prove2me | solution 1 for AllOnesLab.allOnes_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:52:46.713794+00:00
-- url     : https://prove2.me/submissions/94f5929e-a1d7-4201-bd7e-35ca5d73fee9

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n i : ℕ) : (allOnes n).coeff i = if i ≤ n then 1 else 0 := by
  rw [allOnes, finsetSum_coeff]
  simp
end AllOnesLab
