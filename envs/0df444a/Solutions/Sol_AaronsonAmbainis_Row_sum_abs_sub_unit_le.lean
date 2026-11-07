-- Prove2me | solution 1 for AaronsonAmbainis.Row.sum_abs_sub_unit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:30.352842+00:00
-- url     : https://prove2.me/submissions/42c80bda-9641-48e1-89ba-d9d1c3865e8f

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Theorems.Thm_AaronsonAmbainis_Row_sum_abs_le_of_abs_sum_le
import Theorems.Thm_AaronsonAmbainis_Row_abs_sum_sub_unit_le

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) :
    ∑ b, |G (zero β) - G (unit b)| ≤ 4 * (D : ℝ) ^ 2 := by
  have h := sum_abs_le_of_abs_sum_le (fun b => G (zero β) - G (unit b)) (2 * (D : ℝ) ^ 2)
    (fun R => abs_sum_sub_unit_le hM G D hG hdeg R)
  linarith
end AaronsonAmbainis.Row
