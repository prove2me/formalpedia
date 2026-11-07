-- Prove2me | solution 1 for AaronsonAmbainis.Level.separated_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:28.126395+00:00
-- url     : https://prove2.me/submissions/ebdb20f0-fbe6-497e-96d3-90df06fc4934

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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M)
    (A B : Finset (Cube ι)) (s θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ x ∈ A, s + θ ≤ f x) (hB : ∀ y ∈ B, f y ≤ s) :
    2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 * K ^ 2 * M := by
  have h := hTM ι f K a ha hsum hrow M hM0 hM s
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  -- `θ^3 #A ≤ ∑_x ((f x - s)⁺)^3`
  have h1 : θ ^ 3 * (A.card : ℝ) ≤ ∑ x, max (f x - s) 0 ^ 3 := by
    calc θ ^ 3 * (A.card : ℝ) = ∑ _x ∈ A, θ ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ A, max (f x - s) 0 ^ 3 := by
          apply Finset.sum_le_sum
          intro x hx
          exact pow_le_pow_left₀ hθ (le_max_of_le_left (by linarith [hA x hx])) 3
      _ ≤ ∑ x, max (f x - s) 0 ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => pow_nonneg (le_max_right _ _) 3)
  -- `#B ≤ #{f ≤ s}`
  have h3 : (B.card : ℝ) ≤ ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ) := by
    have hsub : B ⊆ univ.filter (fun y : Cube ι => f y ≤ s) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB y hy⟩
    exact_mod_cast Finset.card_le_card hsub
  have h5 : θ ^ 3 * (A.card : ℝ) / 2 ^ Fintype.card ι * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ (∑ x, max (f x - s) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ) / 2 ^ Fintype.card ι) :=
    mul_le_mul (div_le_div_of_nonneg_right h1 h2.le) (div_le_div_of_nonneg_right h3 h2.le)
      (div_nonneg (Nat.cast_nonneg _) h2.le)
      (div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le)
  have h6 : 2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      = 2 * (θ ^ 3 * (A.card : ℝ) / 2 ^ Fintype.card ι
          * ((B.card : ℝ) / 2 ^ Fintype.card ι)) := by ring
  rw [h6]
  linarith
end AaronsonAmbainis.Level
