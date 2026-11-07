-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.infl_evPMt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:13.066083+00:00
-- url     : https://prove2.me/submissions/67411b6e-1353-4536-951c-6ce49e9b19aa

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_comp_negBits
import Theorems.Thm_AaronsonAmbainis_Bridge_negBits_flipBit
import Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_eq

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (i : Fin N) :
    Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      = Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) := by
  simp only [evPMt_eq, negBits_flipBit]
  exact Ex_comp_negBits (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)
end AaronsonAmbainis.Bridge
