-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.evalAt_agMon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:25:41.904739+00:00
-- url     : https://prove2.me/submissions/0cf76333-987a-4045-b74b-9e4cd012cccc

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (c : ℝ) (x z : Cube ι) :
    evalAt c (agMon x z) = c ^ agCount x z := by
  have h : ∀ i, evalAt c (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = if x i = z i then c else 1 := by
    intro i
    by_cases hi : x i = z i
    · rw [if_pos hi, if_pos hi]
      simp [evalAt]
    · rw [if_neg hi, if_neg hi, map_one]
  unfold agMon agCount
  rw [map_prod]
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
end AaronsonAmbainis.DetLow
