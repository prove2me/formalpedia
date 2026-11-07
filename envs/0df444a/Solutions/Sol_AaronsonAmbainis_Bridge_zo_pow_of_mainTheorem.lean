-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.zo_pow_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:57:21.359308+00:00
-- url     : https://prove2.me/submissions/d69fe42b-4b01-4b56-8d75-cebb684717da

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_nonneg
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_hyps_force
import Theorems.Thm_AaronsonAmbainis_Bridge_ratio_pow_le
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_sq_of_mainTheorem

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ≥ (ε / (d : ℝ)) ^ 7 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheorem h N d p hp hrange ε hε hvar
  obtain ⟨hD, hε4⟩ := zo_hyps_force N d p hp hrange ε hε hvar
  exact ⟨i, ratio_pow_le hε hε4 hD (Ex_nonneg fun X => sq_nonneg _) hi⟩
end AaronsonAmbainis.Bridge
