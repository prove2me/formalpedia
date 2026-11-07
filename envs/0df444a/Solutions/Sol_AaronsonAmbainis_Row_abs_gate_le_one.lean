-- Prove2me | solution 1 for AaronsonAmbainis.Row.abs_gate_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:54.792109+00:00
-- url     : https://prove2.me/submissions/3bd163fd-9b6c-42a9-8148-29a914f43f98

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_cnt_nonneg
import Theorems.Thm_AaronsonAmbainis_Row_cnt_le

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (i : ι) (w : Cube β) : |gate S m c i w| ≤ 1 := by
  unfold gate
  have h0 := cnt_nonneg S i w
  have h1 := cnt_le S N hN i w
  have h2 : c * cnt S i w ≤ c * N := mul_le_mul_of_nonneg_left h1 hc
  have h3 : 0 ≤ c * cnt S i w := mul_nonneg hc h0
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ⟨by linarith, by linarith⟩)
end AaronsonAmbainis.Row
