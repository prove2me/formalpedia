-- Prove2me | solution 1 for AaronsonAmbainis.Row.sum_sub_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:32.049204+00:00
-- url     : https://prove2.me/submissions/61123977-21c9-446f-a6c7-2d2b2f62a153

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Theorems.Thm_AaronsonAmbainis_Row_chi_unit
import Theorems.Thm_AaronsonAmbainis_Row_chi_zero


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (g : Finset β → ℝ) (R : Finset β) :
    ∑ b ∈ R, ((∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
  have h1 : ∀ b : β,
      (∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b)
        = ∑ U : Finset β, g U * (if b ∈ U then 2 else 0) := by
    intro b
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [chi_zero, chi_unit]
    split_ifs <;> ring
  have h2 : ∀ U : Finset β, ∑ b ∈ R, (if b ∈ U then (2 : ℝ) else 0) = 2 * ((U ∩ R).card : ℝ) := by
    intro U
    rw [Finset.sum_ite_mem, Finset.sum_const, Finset.inter_comm, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [← Finset.mul_sum, h2 U]
  ring
end AaronsonAmbainis.Row
