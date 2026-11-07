-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.pm_of_mainBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:51:34.37559+00:00
-- url     : https://prove2.me/submissions/57355654-9a66-4a35-a75c-883084310384

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_inflR_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_pm


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {C : ℝ} (h : MainBound C) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 := by
  have hdeg : HasDegreeLE (evPM p) d := hasDegreeLE_eval_pm p hp
  have hvar' : ε ≤ variance (evPM p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hpos : 0 < variance (evPM p) := lt_of_lt_of_le hε hvar'
  obtain ⟨i, hi⟩ := h (Fin n) d (evPM p) hbd hdeg hpos
  refine ⟨i, ?_⟩
  rw [← inflR_eq_Ex (evPM p) i]
  have h5 : ε ^ 5 ≤ variance (evPM p) ^ 5 := pow_le_pow_left₀ hε.le hvar' 5
  linarith
end AaronsonAmbainis.Bridge
