-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_evPMt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:06.460053+00:00
-- url     : https://prove2.me/submissions/1df6bfd7-b382-45dd-810f-833208ca6e4f

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_comp_negBits
import Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_eq
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_evPMt

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) = Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) := by
  rw [Ex_evPMt]
  simp only [evPMt_eq]
  exact Ex_comp_negBits (fun X => (evPM p X - Ex (evPM p)) ^ 2)
end AaronsonAmbainis.Bridge
