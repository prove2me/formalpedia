-- Prove2me | solution 1 for AaronsonAmbainis.Row.abs_sum_sub_unit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:51.646827+00:00
-- url     : https://prove2.me/submissions/e6e3ab9d-f0b2-46d1-8a91-ea2fbf120fa8

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Theorems.Thm_AaronsonAmbainis_Row_natDegree_phi_le
import Theorems.Thm_AaronsonAmbainis_Row_eval_phi
import Theorems.Thm_AaronsonAmbainis_Row_derivative_phi_eval_zero
import Theorems.Thm_AaronsonAmbainis_Row_sum_sub_unit
import Theorems.Thm_AaronsonAmbainis_Row_abs_multilinear_le_one
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) (R : Finset β) :
    |∑ b ∈ R, (G (zero β) - G (unit b))| ≤ 2 * (D : ℝ) ^ 2 := by
  obtain ⟨g, hg, hGg⟩ := hdeg
  have hbound : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |(phi g R).eval s| ≤ 1 := by
    intro s hs0 hs2
    rw [eval_phi]
    refine abs_multilinear_le_one g (fun z => ?_) (fun b => if b ∈ R then 1 - s else 1)
      (fun b => ?_)
    · rw [← hGg z]
      exact hG z
    · split_ifs
      · rw [abs_le]
        constructor <;> linarith
      · simp
  have hmark := hM D (phi g R) (natDegree_phi_le g R D hg) hbound
  rw [derivative_phi_eval_zero, abs_neg] at hmark
  have hsum : ∑ b ∈ R, (G (zero β) - G (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
    rw [← sum_sub_unit g R]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hGg (zero β), hGg (unit b)]
  rw [hsum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith
end AaronsonAmbainis.Row
