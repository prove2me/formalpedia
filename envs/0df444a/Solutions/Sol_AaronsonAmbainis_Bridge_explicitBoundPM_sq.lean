-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.explicitBoundPM_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:59:23.856073+00:00
-- url     : https://prove2.me/submissions/22879d94-44c9-445d-b010-9fd7c20239a6

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_Bridge_pmt_sq_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_mainTheorem


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 :=
  pmt_sq_of_mainTheorem AaronsonAmbainis.mainTheorem n d p hp hbd ε hε hvar
end AaronsonAmbainis.Bridge
