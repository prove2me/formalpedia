-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.pm_sq_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:53:44.977672+00:00
-- url     : https://prove2.me/submissions/5d5bf959-fab9-424e-89d4-0aa9df0bd3fb

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_mainBound_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_Bridge_pm_of_mainBound

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 :=
  pm_of_mainBound (mainBound_of_mainTheorem h) n d p hp hbd ε hε hvar
end AaronsonAmbainis.Bridge
