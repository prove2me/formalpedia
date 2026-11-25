-- Prove2me | solution 1 for AllOnesLab.even_of_irreducible_allOnes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:49.773486+00:00
-- url     : https://prove2.me/submissions/67a63bfc-e9e9-4301-a920-0a7145e890b6

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_allOnes_natDegree
import Theorems.Thm_AllOnesLab_allOnes_eval_one

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (h : Irreducible (allOnes n)) :
    Even n := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ : 2 ∣ n + 1 := by
    have := Nat.odd_iff.mp hodd
    omega
  have hcast : ((n + 1 : ℕ) : ZMod 2) = 0 := by
    rw [hk]
    push_cast
    simp [show (2 : ZMod 2) = 0 by decide]
  have hroot : (allOnes n).IsRoot 1 := by
    rw [Polynomial.IsRoot.def, allOnes_eval_one]
    push_cast at hcast
    exact hcast
  exact h.not_isRoot_of_natDegree_ne_one (by rw [allOnes_natDegree]; omega) hroot
end AllOnesLab
