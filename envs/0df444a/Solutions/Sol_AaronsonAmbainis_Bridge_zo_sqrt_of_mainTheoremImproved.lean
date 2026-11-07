-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.zo_sqrt_of_mainTheoremImproved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:58:04.353317+00:00
-- url     : https://prove2.me/submissions/071a013c-7a20-4a40-bd94-5ea184636c61

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_Ex_nonneg
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_hyps_force
import Theorems.Thm_AaronsonAmbainis_Bridge_sqrt_form_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_sq_of_mainTheoremImproved

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheoremImproved) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2)
      ≥ 32 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheoremImproved h N d p hp hrange ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) :=
    lt_of_lt_of_le one_pos (zo_hyps_force N d p hp hrange ε hε hvar).1
  exact ⟨i, (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε.le hD
    (Ex_nonneg fun X => sq_nonneg _)).mpr hi⟩
end AaronsonAmbainis.Bridge
