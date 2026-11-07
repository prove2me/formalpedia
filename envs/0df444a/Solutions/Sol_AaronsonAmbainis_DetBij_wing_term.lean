-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.wing_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:16.373408+00:00
-- url     : https://prove2.me/submissions/b1121885-6cf0-4380-9f16-27b2540e2081

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_fAg_flipSet_of_mem
import Theorems.Thm_AaronsonAmbainis_DetBij_fAg_flipSet_of_notMem

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) {A S : Finset ι} (hSA : S ⊆ A) :
    (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i) * ∏ i ∈ A \ S, fAg x z i)
          * ∏ i ∈ Aᶜ, fAg x z i := by
  have h1 : agMon (flipSet x S) z
      = (∏ i ∈ A, fAg (flipSet x S) z i) * ∏ i ∈ Aᶜ, fAg (flipSet x S) z i :=
    (Finset.prod_mul_prod_compl A (fAg (flipSet x S) z)).symm
  have h2 : ∏ i ∈ Aᶜ, fAg (flipSet x S) z i = ∏ i ∈ Aᶜ, fAg x z i :=
    Finset.prod_congr rfl fun i hi =>
      fAg_flipSet_of_notMem x z fun h => (Finset.mem_compl.mp hi) (hSA h)
  have h3 : ∏ i ∈ A, fAg (flipSet x S) z i
      = (∏ i ∈ A \ S, fAg x z i) * ∏ i ∈ S, gAg x z i := by
    rw [← Finset.prod_sdiff hSA]
    congr 1
    · exact Finset.prod_congr rfl fun i hi =>
        fAg_flipSet_of_notMem x z (Finset.mem_sdiff.mp hi).2
    · exact Finset.prod_congr rfl fun i hi => fAg_flipSet_of_mem x z hi
  rw [h1, h2, h3, Finset.prod_mul_distrib]
  ring
end AaronsonAmbainis.DetBij
