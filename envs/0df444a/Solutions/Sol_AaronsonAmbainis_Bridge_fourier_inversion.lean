-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:39.602411+00:00
-- url     : https://prove2.me/submissions/39f505d5-8620-495b-9bc4-6ae29a962cb2

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_sum_chi_mul_chi

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (f : Cube ι → ℝ) (x : Cube ι) :
    ∑ S, fourier f S * chi S x = f x := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  calc ∑ S : Finset ι, fourier f S * chi S x
      = ∑ S : Finset ι, (∑ y, f y * (chi S x * chi S y)) / 2 ^ Fintype.card ι := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [fourier, div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring
    _ = (∑ y, ∑ S : Finset ι, f y * (chi S x * chi S y)) / 2 ^ Fintype.card ι := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ = (∑ y, f y * (if x = y then (2 : ℝ) ^ Fintype.card ι else 0)) / 2 ^ Fintype.card ι := by
        congr 1
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.mul_sum, sum_chi_mul_chi]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl, mul_div_assoc, div_self hne, mul_one]
        · intro y _ hy
          rw [if_neg (Ne.symm hy), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ x) h
end AaronsonAmbainis.Bridge
