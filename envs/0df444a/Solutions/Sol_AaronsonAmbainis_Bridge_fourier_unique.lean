-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.fourier_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:22.138361+00:00
-- url     : https://prove2.me/submissions/3ee5edcc-f2ad-4585-8be3-20240db754f9

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_sum_chi_mul_chi_cube

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {c : Finset ι → ℝ}
    (hf : ∀ x, f x = ∑ S, c S * chi S x) (T : Finset ι) : c T = fourier f T := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  have h1 : ∑ y, f y * chi T y = c T * 2 ^ Fintype.card ι := by
    calc ∑ y, f y * chi T y
        = ∑ y, ∑ S : Finset ι, c S * (chi S y * chi T y) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hf y, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          ring
      _ = ∑ S : Finset ι, c S * ∑ y, chi S y * chi T y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ S : Finset ι, c S * (if S = T then (2 : ℝ) ^ Fintype.card ι else 0) := by
          simp only [sum_chi_mul_chi_cube]
      _ = c T * 2 ^ Fintype.card ι := by
          rw [Finset.sum_eq_single T]
          · rw [if_pos rfl]
          · intro S _ hS
            rw [if_neg hS, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ T) h
  rw [fourier, h1, mul_div_assoc, div_self hne, mul_one]
end AaronsonAmbainis.Bridge
