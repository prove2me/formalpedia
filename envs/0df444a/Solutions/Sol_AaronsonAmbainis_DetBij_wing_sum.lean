-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.wing_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:40.445434+00:00
-- url     : https://prove2.me/submissions/411c0148-368a-4f7a-93ee-719ef1f016c5

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_agMon_eq_prod
import Theorems.Thm_AaronsonAmbainis_DetBij_neg_X_mul_gAg_add_fAg
import Theorems.Thm_AaronsonAmbainis_DetBij_wing_term
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_agSet


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) (A : Finset ι) :
    ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = (∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x z) A then agMon x z else 0) := by
  have h0 : ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ∑ S ∈ A.powerset, ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i)
          * ∏ i ∈ A \ S, fAg x z i) * ∏ i ∈ Aᶜ, fAg x z i :=
    Finset.sum_congr rfl fun S hS => wing_term x z (Finset.mem_powerset.mp hS)
  rw [h0, ← Finset.sum_mul, ← Finset.prod_add]
  by_cases hd : Disjoint (agSet x z) A
  · have hne : ∀ i ∈ A, ¬ x i = z i := fun i hi h =>
      (Finset.disjoint_left.mp hd (mem_agSet.mpr h)) hi
    have e1 : ∏ i ∈ A, (-(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i)
        = ∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2) :=
      Finset.prod_congr rfl fun i hi => by
        rw [neg_X_mul_gAg_add_fAg, if_neg (hne i hi)]
    have e2 : agMon x z = ∏ i ∈ Aᶜ, fAg x z i := by
      have e3 : ∏ i ∈ A, fAg x z i = 1 :=
        Finset.prod_eq_one fun i hi => by
          unfold fAg
          rw [if_neg (hne i hi)]
      rw [agMon_eq_prod, ← Finset.prod_mul_prod_compl A (fAg x z), e3, one_mul]
    rw [if_pos hd, e1, e2]
  · obtain ⟨i, hi1, hi2⟩ := Finset.not_disjoint_iff.mp hd
    have e1 : ∏ i ∈ A, (-(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i) = 0 :=
      Finset.prod_eq_zero hi2 (by rw [neg_X_mul_gAg_add_fAg, if_pos (mem_agSet.mp hi1)])
    rw [if_neg hd, mul_zero, e1, zero_mul]
end AaronsonAmbainis.DetBij
