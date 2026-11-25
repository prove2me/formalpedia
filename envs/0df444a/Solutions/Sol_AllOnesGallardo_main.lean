-- Prove2me | solution 1 for AllOnesGallardo.main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:07:05.01304+00:00
-- url     : https://prove2.me/submissions/229e58ed-f6c2-4b48-9b60-c4529b40a646

import Definitions.Def_AllOnesLab
import Definitions.Def_AllOnesComparator_Solution
import Theorems.Thm_AllOnesLab_main


set_option autoImplicit true
open Polynomial
open AllOnesGallardo
namespace AllOnesGallardo
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) :=
  AllOnesLab.main n hn
end AllOnesGallardo
