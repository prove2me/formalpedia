-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.aaInfl_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:33:54.646901+00:00
-- url     : https://prove2.me/submissions/34793087-5c66-4930-b240-a44733a1392d

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_ev01_X
import Theorems.Thm_AaronsonAmbainis_Bridge_flipBit_self
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_const_one
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (i : Fin N) :
    Ex (fun Y => (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y
      - ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) (flipBit Y i)) ^ 2) = 1 := by
  have h : ∀ Y : Fin N → Bool,
      (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y
        - ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) (flipBit Y i)) ^ 2 = 1 := by
    intro Y
    rw [ev01_X, ev01_X, flipBit_self]
    cases Y i <;> simp
  simp only [h]
  exact Ex_const_one
end AaronsonAmbainis.Bridge
