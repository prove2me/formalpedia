-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.pmt_sqrt_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:58:07.665192+00:00
-- url     : https://prove2.me/submissions/eb50dfb7-ce03-489d-832e-e6c404a76a05

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_pm_sqrt_of_mainTheorem
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
    ∃ i, Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  rw [variance_evPMt] at hvar
  obtain ⟨i, hi⟩ :=
    pm_sqrt_of_mainTheorem h n d p hp ((evPMt_bound_iff p).mp hbd) ε hε hvar
  exact ⟨i, by rwa [infl_evPMt]⟩
end AaronsonAmbainis.Bridge
