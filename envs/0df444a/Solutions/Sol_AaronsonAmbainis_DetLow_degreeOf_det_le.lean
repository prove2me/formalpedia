-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.degreeOf_det_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:24.492251+00:00
-- url     : https://prove2.me/submissions/1cbc6d51-5514-4414-a3e9-74765125f28b

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
import Theorems.Thm_AaronsonAmbainis_DetLow_degreeOf_agMon_le
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
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    degreeOf j (agMatrix g).det ≤ Fintype.card (Ones g) := by
  have hc : ∀ n : ℤ, degreeOf j ((n : MvPolynomial ι ℤ)) = 0 := by
    intro n
    rw [← eq_intCast (C : ℤ →+* MvPolynomial ι ℤ) n, degreeOf_C]
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le j univ _).trans ?_
  apply Finset.sup_le
  intro σ _
  refine (degreeOf_mul_le j _ _).trans ?_
  rw [hc, zero_add]
  refine (degreeOf_prod_le j univ _).trans ?_
  calc ∑ i : Ones g, degreeOf j (agMatrix g (σ i) i) ≤ ∑ _i : Ones g, 1 :=
        Finset.sum_le_sum (fun i _ => degreeOf_agMon_le _ _ j)
    _ = Fintype.card (Ones g) := by simp
end AaronsonAmbainis.DetLow
