-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.inflR_dict_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:47.1032+00:00
-- url     : https://prove2.me/submissions/9b3176e3-3c2e-4a39-b815-c1bceee1731b

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_sq
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_flip
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) : inflR (dict j) j = 1 := by
  have h : ∀ x : Cube ι, ((dict j x - dict j (flipSet x {j})) / 2) ^ 2 = 1 := by
    intro x
    rw [dict_flip]
    have h2 : (dict j x - -dict j x) / 2 = dict j x := by ring
    rw [h2, dict_sq]
  simp only [inflR, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [card_cube]
  exact div_self (by positivity)
end AaronsonAmbainis.Bridge
