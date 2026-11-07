-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.evPM_X_eq_dict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:11.128403+00:00
-- url     : https://prove2.me/submissions/adfa5432-dd4e-424c-a21e-f427fdddc970

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_evPM_X

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (i : Fin N) :
    (evPM (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ) = dict i := by
  funext Y
  rw [evPM_X]
  rfl
end AaronsonAmbainis.Bridge
