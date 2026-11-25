-- Prove2me | solution 1 for AllOnesLab.allOnesP_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:00.731283+00:00
-- url     : https://prove2.me/submissions/9bc8a1ae-c68b-4275-81b4-1b8b96fbc8e9

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) : allOnesP n = (allOnes n).comp P := by
  rw [allOnes, allOnesP, Polynomial.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_comp, X_comp]
end AllOnesLab
