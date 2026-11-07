-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.zo_hyps_force
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:51:32.105352+00:00
-- url     : https://prove2.me/submissions/3a4545df-31a0-42d1-a654-08c63950b998

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_aa_hyps_force
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_zo
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_le_quarter


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    (1 : ℝ) ≤ (d : ℝ) ∧ ε ≤ 1 / 4 := by
  have hdeg : HasDegreeLE (ev01 p) d := hasDegreeLE_eval_zo p hp
  have hvar' : ε ≤ variance (ev01 p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hd : 1 ≤ d := (aa_hyps_force hdeg (lt_of_lt_of_le hε hvar')).1
  exact ⟨by exact_mod_cast hd, hvar'.trans (variance_le_quarter hrange)⟩
end AaronsonAmbainis.Bridge
