-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.ev01_X_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:06.877571+00:00
-- url     : https://prove2.me/submissions/f42d9a76-e167-44a3-bc46-fc7f1266856e

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_ev01_X

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (i : Fin N) :
    (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ)
      = fun Y => 1 / 2 + (-1 / 2) * dict i Y := by
  funext Y
  rw [ev01_X]
  unfold dict
  split_ifs <;> norm_num
end AaronsonAmbainis.Bridge
