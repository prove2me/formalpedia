-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.pm_hyps_force
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:51:34.944682+00:00
-- url     : https://prove2.me/submissions/ea193270-753d-450b-aaae-9ea491e8d8e0

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_aa_hyps_force
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_pm


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    (1 : ℝ) ≤ (d : ℝ) := by
  have hdeg : HasDegreeLE (evPM p) d := hasDegreeLE_eval_pm p hp
  have hvar' : ε ≤ variance (evPM p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hd : 1 ≤ d := (aa_hyps_force hdeg (lt_of_lt_of_le hε hvar')).1
  exact_mod_cast hd
end AaronsonAmbainis.Bridge
