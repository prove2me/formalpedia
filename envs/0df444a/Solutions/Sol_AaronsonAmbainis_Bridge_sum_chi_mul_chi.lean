-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sum_chi_mul_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:09.307754+00:00
-- url     : https://prove2.me/submissions/d5efdba6-66da-4f3a-8e8a-9fcc7b9e7e1a

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_sg_mul_self
import Theorems.Thm_AaronsonAmbainis_Bridge_sg_mul_of_ne
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_eq_prod_sg

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x y : Cube ι) :
    ∑ S : Finset ι, chi S x * chi S y = if x = y then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have h1 : ∑ S : Finset ι, chi S x * chi S y = ∏ i : ι, (1 + sg (x i) * sg (y i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [chi_eq_prod_sg, chi_eq_prod_sg, ← Finset.prod_mul_distrib]
  rw [h1]
  split_ifs with h
  · have h2 : ∀ i : ι, (1 + sg (x i) * sg (y i)) = 2 := fun i => by
      rw [← h, sg_mul_self]
      norm_num
    simp only [h2, Finset.prod_const, Finset.card_univ]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sg_mul_of_ne hi]
    norm_num
end AaronsonAmbainis.Bridge
