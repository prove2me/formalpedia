-- Prove2me | solution 1 for AaronsonAmbainis.Level.four_mul_integrated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:54.468391+00:00
-- url     : https://prove2.me/submissions/62220132-55f2-4b23-aa3a-f3e24d3c36ff

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Theorems.Thm_AaronsonAmbainis_Level_four_pow_card


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
  have h := hInt ι f a ha hrow w hw
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.univ_eq_empty (α := ι), Finset.sum_empty, mul_zero] at h ⊢
    linarith
  · rw [four_pow_card, mul_assoc]
    linarith
end AaronsonAmbainis.Level
