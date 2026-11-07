-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:19.479208+00:00
-- url     : https://prove2.me/submissions/71bab782-c06f-4735-b687-1b6bf90574e7

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_variance_le_sq_dist
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {P : Cube ι → ℝ} (h : ∀ x, 0 ≤ P x ∧ P x ≤ 1) :
    variance P ≤ 1 / 4 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (Level.variance_le_sq_dist P (1 / 2)).trans ?_
  rw [div_le_iff₀ hpos]
  have h1 : ∑ x : Cube ι, (P x - 1 / 2) ^ 2 ≤ ∑ _x : Cube ι, (1 / 4 : ℝ) :=
    Finset.sum_le_sum (fun x _ => by
      obtain ⟨h0, h1⟩ := h x
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube] at h1
  linarith
end AaronsonAmbainis.Bridge
