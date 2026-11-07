-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.Ex_evPMt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:36.559194+00:00
-- url     : https://prove2.me/submissions/f6bfa390-899e-45ff-9f4e-2f0f0973a0d6

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_comp_negBits
import Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_eq

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (p : MvPolynomial (Fin N) ℝ) : Ex (evPMt p) = Ex (evPM p) := by
  have e : evPMt p = fun X => evPM p (negBits X) := funext (evPMt_eq p)
  rw [e]
  exact Ex_comp_negBits (evPM p)
end AaronsonAmbainis.Bridge
