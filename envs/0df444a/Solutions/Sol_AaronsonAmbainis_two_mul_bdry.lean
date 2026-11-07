-- Prove2me | solution 1 for AaronsonAmbainis.two_mul_bdry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:38.294224+00:00
-- url     : https://prove2.me/submissions/6c2b37a9-8006-41c5-b8da-7ad65c332ecc

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Theorems.Thm_AaronsonAmbainis_card_sensitive

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    2 * (bdry g j : ℝ) = 2 ^ Fintype.card ι * infl g j := by
  have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  unfold infl
  rw [card_sensitive]
  push_cast
  field_simp
end AaronsonAmbainis
