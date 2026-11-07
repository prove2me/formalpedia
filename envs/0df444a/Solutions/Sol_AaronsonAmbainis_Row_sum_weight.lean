-- Prove2me | solution 1 for AaronsonAmbainis.Row.sum_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:15.539649+00:00
-- url     : https://prove2.me/submissions/8043d595-8964-42f5-86b3-bb68980c419c

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
import Theorems.Thm_AaronsonAmbainis_Row_sum_weight_mul_chi
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (u : ι → ℝ) : ∑ z : Cube ι, weight u z = 1 := by
  have h := sum_weight_mul_chi u (∅ : Finset ι)
  simpa [chi] using h
end AaronsonAmbainis.Row
