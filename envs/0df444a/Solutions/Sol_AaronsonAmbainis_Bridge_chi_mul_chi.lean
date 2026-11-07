-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.chi_mul_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:28.488134+00:00
-- url     : https://prove2.me/submissions/ab0562fb-e287-434c-99e0-21669960d1b7

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_sg_mul_self
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_eq_prod_univ

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [chi_eq_prod_univ S, chi_eq_prod_univ T, chi_eq_prod_univ (symmDiff S T),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, sg_mul_self]
end AaronsonAmbainis.Bridge
