-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.explicitBound_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:57:21.981644+00:00
-- url     : https://prove2.me/submissions/93bd5026-5fef-4150-bbac-ec669f6bc447

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_sq_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_mainTheorem


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_sq_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar
end AaronsonAmbainis.Bridge
