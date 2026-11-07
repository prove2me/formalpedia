-- Prove2me | solution 1 for AaronsonAmbainis.Level.thirdMoment_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:01:01.410289+00:00
-- url     : https://prove2.me/submissions/01cabf9a-830a-41ce-ac26-e2c64815a02d

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment

set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (s - f x) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => s ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M := by
  have hrow' : ∀ x y, |(fun x => -f x) x - (fun x => -f x) y| ≤ ∑ j ∈ diffSet x y, a x j := by
    intro x y
    show |-f x - -f y| ≤ ∑ j ∈ diffSet x y, a x j
    rw [neg_sub_neg, abs_sub_comm]
    exact hrow x y
  have hM' : ∀ j, meanAbsIncr (fun x => -f x) j ≤ M := by
    intro j
    have e : meanAbsIncr (fun x => -f x) j = meanAbsIncr f j := by
      unfold meanAbsIncr
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      show |-f x - -f (flipSet x {j})| = |f x - f (flipSet x {j})|
      rw [neg_sub_neg, abs_sub_comm]
    rw [e]
    exact hM j
  have h := hTM ι (fun x => -f x) K a ha hsum hrow' M hM0 hM' (-s)
  have e1 : ∀ x, max ((fun x => -f x) x - -s) 0 = max (s - f x) 0 := by
    intro x
    show max (-f x - -s) 0 = max (s - f x) 0
    rw [neg_sub_neg]
  have e2 : (univ.filter (fun y : Cube ι => (fun x => -f x) y ≤ -s))
      = univ.filter (fun y : Cube ι => s ≤ f y) := by
    apply Finset.filter_congr
    intro y _
    show -f y ≤ -s ↔ s ≤ f y
    exact neg_le_neg_iff
  simp only [e1] at h
  rw [e2] at h
  exact h
end AaronsonAmbainis.Level
