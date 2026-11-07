-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_dict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:12.278207+00:00
-- url     : https://prove2.me/submissions/a6187bb5-4243-4ef6-a9a1-a8251144ef25

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_sq
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
import Theorems.Thm_AaronsonAmbainis_Bridge_mean_dict

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) : variance (dict j) = 1 := by
  simp only [variance, mean_dict, sub_zero, dict_sq, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [card_cube]
  exact div_self (by positivity)
end AaronsonAmbainis.Bridge
