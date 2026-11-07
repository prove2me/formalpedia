-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.pmt_sq_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:55:55.324253+00:00
-- url     : https://prove2.me/submissions/b62baad7-d445-4ccb-94b6-15e8d322a98f

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_pm_sq_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_bound_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_evPMt
import Theorems.Thm_AaronsonAmbainis_Bridge_infl_evPMt

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 := by
  rw [variance_evPMt] at hvar
  obtain ⟨i, hi⟩ :=
    pm_sq_of_mainTheorem h n d p hp ((evPMt_bound_iff p).mp hbd) ε hε hvar
  exact ⟨i, by rwa [infl_evPMt]⟩
end AaronsonAmbainis.Bridge
