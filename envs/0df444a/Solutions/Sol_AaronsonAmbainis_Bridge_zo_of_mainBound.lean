-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.zo_of_mainBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:51:33.656195+00:00
-- url     : https://prove2.me/submissions/9faab02a-6b7b-49dc-9c18-65f4e18bd4ba

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_eq_flipBit
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_zero_one_of_mainBound
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_zo


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {C : ℝ} (h : MainBound C) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 := by
  have hdeg : HasDegreeLE (ev01 p) d := hasDegreeLE_eval_zo p hp
  have hvar' : ε ≤ variance (ev01 p) := by
    rw [variance_eq_Ex]
    exact hvar
  obtain ⟨i, hi⟩ := zero_one_of_mainBound h d (ev01 p) hrange hdeg (lt_of_lt_of_le hε hvar')
  refine ⟨i, ?_⟩
  have hI : (∑ X : Cube (Fin N), (ev01 p X - ev01 p (flipSet X {i})) ^ 2)
        / 2 ^ Fintype.card (Fin N)
      = Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) := by
    rw [Fintype.card_fin]
    simp only [flipSet_singleton_eq_flipBit]
    rfl
  rw [hI] at hi
  have h5 : ε ^ 5 ≤ variance (ev01 p) ^ 5 := pow_le_pow_left₀ hε.le hvar' 5
  linarith
end AaronsonAmbainis.Bridge
