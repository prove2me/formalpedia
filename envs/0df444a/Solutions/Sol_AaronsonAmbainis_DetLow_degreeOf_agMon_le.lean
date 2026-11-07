-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.degreeOf_agMon_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:02.83518+00:00
-- url     : https://prove2.me/submissions/7e46e1dd-a5c8-4d00-a4a4-797ad7de78b0

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x z : Cube ι) (j : ι) : degreeOf j (agMon x z) ≤ 1 := by
  unfold agMon
  refine (degreeOf_prod_le j univ _).trans ?_
  calc ∑ i, degreeOf j (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      ≤ ∑ i, (if j = i then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : x i = z i
        · rw [if_pos h, degreeOf_X]
        · rw [if_neg h, degreeOf_one]
          exact Nat.zero_le _
    _ = 1 := by simp
end AaronsonAmbainis.DetLow
