-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_meanAbsIncr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:16.086961+00:00
-- url     : https://prove2.me/submissions/3893e141-0999-4060-a95e-ae515ffea1ce

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) {G : ℝ}
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) : ∑ j, meanAbsIncr f j ≤ G := by
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  unfold meanAbsIncr
  rw [← Finset.sum_div, div_le_iff₀ h2, Finset.sum_comm]
  calc ∑ x, ∑ j, |f x - f (flipSet x {j})| ≤ ∑ _x : Cube ι, G :=
        Finset.sum_le_sum (fun x _ => hG x)
    _ = G * 2 ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube, mul_comm]
end AaronsonAmbainis.Level
