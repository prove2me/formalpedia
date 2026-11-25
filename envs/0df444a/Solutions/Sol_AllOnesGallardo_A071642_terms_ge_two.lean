-- Prove2me | solution 1 for AllOnesGallardo.A071642_terms_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:09:11.406348+00:00
-- url     : https://prove2.me/submissions/d5b8088d-7ca1-48ed-8896-beec85373987

import Definitions.Def_AllOnesLab
import Definitions.Def_AllOnesComparator_Solution
import Theorems.Thm_AllOnesLab_A071642_terms_ge_two


set_option autoImplicit true
open Polynomial
open AllOnesGallardo
namespace AllOnesGallardo
theorem _root_.solution :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} :=
  AllOnesLab.A071642_terms_ge_two
end AllOnesGallardo
