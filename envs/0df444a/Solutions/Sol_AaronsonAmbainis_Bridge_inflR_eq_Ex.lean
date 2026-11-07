-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.inflR_eq_Ex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:52.551355+00:00
-- url     : https://prove2.me/submissions/85ca9e78-523d-4904-98b0-8737c898d60a

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_eq_flipBit

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (F : Cube (Fin N) → ℝ) (i : Fin N) :
    inflR F i = Ex (fun X => ((F X - F (flipBit X i)) / 2) ^ 2) := by
  have h : inflR F i
      = (∑ x, ((F x - F (flipSet x {i})) / 2) ^ 2) / 2 ^ Fintype.card (Fin N) := rfl
  rw [h, Fintype.card_fin]
  simp only [flipSet_singleton_eq_flipBit]
  rfl
end AaronsonAmbainis.Bridge
