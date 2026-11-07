-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.zero_one_of_mainBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:24:41.116631+00:00
-- url     : https://prove2.me/submissions/c740621f-87d8-4cf4-a8e4-602951fbb2f4

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_smul
import Theorems.Thm_AaronsonAmbainis_Bridge_inflR_affine
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_affine
import Theorems.Thm_AaronsonAmbainis_Level_inflR_eq_quarter


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {C : ℝ} (h : MainBound C) {ι : Type} [Fintype ι]
    [DecidableEq ι] (d : ℕ) (P : Cube ι → ℝ) (hrange : ∀ X, 0 ≤ P X ∧ P X ≤ 1)
    (hdeg : HasDegreeLE P d) (hpos : 0 < variance P) :
    ∃ i, 3072 * variance P ^ 5 ≤ C * (d : ℝ) ^ 12
      * ((∑ X : Cube ι, (P X - P (flipSet X {i})) ^ 2) / 2 ^ Fintype.card ι) ^ 2 := by
  have hdeg' : HasDegreeLE (fun X => 1 + (-2) * P X) d :=
    hasDegreeLE_add (hasDegreeLE_const 1 d) (hasDegreeLE_smul (-2) hdeg)
  have hbd : ∀ X, |1 + (-2) * P X| ≤ 1 := by
    intro X
    obtain ⟨h0, h1⟩ := hrange X
    rw [abs_le]
    constructor <;> linarith
  have hV : variance (fun X => 1 + (-2) * P X) = 4 * variance P := by
    rw [variance_affine]
    norm_num
  have hVpos : 0 < variance (fun X => 1 + (-2) * P X) := by
    rw [hV]
    linarith
  obtain ⟨i, hi⟩ := h ι d (fun X => 1 + (-2) * P X) hbd hdeg' hVpos
  refine ⟨i, ?_⟩
  have hI : inflR (fun X => 1 + (-2) * P X) i
      = (∑ X : Cube ι, (P X - P (flipSet X {i})) ^ 2) / 2 ^ Fintype.card ι := by
    rw [inflR_affine, Level.inflR_eq_quarter]
    ring
  rw [hV, hI] at hi
  have e : 3 * (4 * variance P) ^ 5 = 3072 * variance P ^ 5 := by ring
  rw [e] at hi
  exact hi
end AaronsonAmbainis.Bridge
