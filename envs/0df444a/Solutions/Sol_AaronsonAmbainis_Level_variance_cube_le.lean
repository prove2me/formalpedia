-- Prove2me | solution 1 for AaronsonAmbainis.Level.variance_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:17:46.325009+00:00
-- url     : https://prove2.me/submissions/90df8c79-6d56-4b20-8849-9ca13aed43af

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Theorems.Thm_AaronsonAmbainis_Level_exists_abs_cube_le
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_sum_sq_cube_le
import Theorems.Thm_AaronsonAmbainis_Level_variance_le_sq_dist
import Theorems.Thm_AaronsonAmbainis_Level_variance_nonneg
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    variance f ^ 3 ≤ 36 * K ^ 4 * M ^ 2 := by
  obtain ⟨m, hm⟩ := exists_abs_cube_le hTM f a ha hsum hrow hM0 hM
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hV0 : 0 ≤ variance f := variance_nonneg f
  have hV := variance_le_sq_dist f m
  have hpm := sum_sq_cube_le (univ : Finset (Cube ι)) (fun x => f x - m)
  rw [Finset.card_univ, card_cube] at hpm
  have hT0 : 0 ≤ (∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (abs_nonneg _) 3) h2.le
  calc variance f ^ 3 ≤ ((∑ x, (f x - m) ^ 2) / 2 ^ Fintype.card ι) ^ 3 :=
        pow_le_pow_left₀ hV0 hV 3
    _ ≤ ((∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι) ^ 2 := by
        rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have h7 := mul_le_mul_of_nonneg_right hpm (sq_nonneg ((2 : ℝ) ^ Fintype.card ι))
        calc (∑ x, (f x - m) ^ 2) ^ 3 * ((2 : ℝ) ^ Fintype.card ι) ^ 2
            ≤ 2 ^ Fintype.card ι * (∑ x, |f x - m| ^ 3) ^ 2 * ((2 : ℝ) ^ Fintype.card ι) ^ 2 := h7
          _ = (∑ x, |f x - m| ^ 3) ^ 2 * ((2 : ℝ) ^ Fintype.card ι) ^ 3 := by ring
    _ ≤ (6 * K ^ 2 * M) ^ 2 := pow_le_pow_left₀ hT0 hm 2
    _ = 36 * K ^ 4 * M ^ 2 := by ring
end AaronsonAmbainis.Level
