-- Prove2me | solution 1 for AllOnesLab.main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:18.304938+00:00
-- url     : https://prove2.me/submissions/47341767-532d-47f5-aaa1-29a401a9f817

import Definitions.Def_AllOnesLab_Hard
import Definitions.Def_AllOnesLab_Main
import Theorems.Thm_AllOnesLab_irreducible_allOnesP_of_irreducible_allOnes
import Theorems.Thm_AllOnesLab_irreducible_allOnes_of_irreducible_allOnesP


set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) :=
  ⟨irreducible_allOnesP_of_irreducible_allOnes n hn,
   irreducible_allOnes_of_irreducible_allOnesP n hn⟩
end AllOnesLab
