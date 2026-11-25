-- Prove2me | solution 1 for AllOnesLab.A071642_terms_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:11.546324+00:00
-- url     : https://prove2.me/submissions/d6343aba-bfa9-4286-a6de-cb49c053cc4c

import Definitions.Def_AllOnesLab_Hard
import Definitions.Def_AllOnesLab_Main
import Theorems.Thm_AllOnesLab_main

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} := by
  ext n
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ⟨h, hi⟩ => ⟨h, (main n h).1 hi⟩, fun ⟨h, hi⟩ => ⟨h, (main n h).2 hi⟩⟩
end AllOnesLab
