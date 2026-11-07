-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_eq_Ex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:39.628991+00:00
-- url     : https://prove2.me/submissions/85d4102f-6c78-410d-a790-0405a1db5dff

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_mean_eq_Ex

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (F : Cube (Fin N) → ℝ) :
    variance F = Ex (fun X => (F X - Ex F) ^ 2) := by
  have h : variance F = (∑ x, (F x - mean F) ^ 2) / 2 ^ Fintype.card (Fin N) := rfl
  rw [h, mean_eq_Ex, Fintype.card_fin]
  rfl
end AaronsonAmbainis.Bridge
