-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.pm_sqrt_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:55:54.818379+00:00
-- url     : https://prove2.me/submissions/f848af98-cc74-4b3e-a2b2-1449e2f5c1c9

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_nonneg
import Theorems.Thm_AaronsonAmbainis_Bridge_pm_hyps_force
import Theorems.Thm_AaronsonAmbainis_Bridge_sqrt_form_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_pm_sq_of_mainTheorem

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := pm_sq_of_mainTheorem h n d p hp hbd ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos (pm_hyps_force n d p hp ε hε hvar)
  have h1 := (sqrt_form_iff (c₁ := 1) (c₂ := 500) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε.le hD (Ex_nonneg fun X => sq_nonneg _)).mpr hi
  rw [one_mul] at h1
  exact ⟨i, h1⟩
end AaronsonAmbainis.Bridge
