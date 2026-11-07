-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.zo_sq_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:55:40.990215+00:00
-- url     : https://prove2.me/submissions/670d9796-643a-477e-98ce-8d3f989a461d

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_mainBound_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_of_mainBound

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 := by
  obtain ⟨i, hi⟩ := zo_of_mainBound (mainBound_of_mainTheorem h) N d p hp hrange ε hε hvar
  exact ⟨i, by linarith⟩
end AaronsonAmbainis.Bridge
