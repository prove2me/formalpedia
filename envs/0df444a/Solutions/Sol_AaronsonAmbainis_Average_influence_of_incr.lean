-- Prove2me | solution 1 for AaronsonAmbainis.Average.influence_of_incr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:09.094581+00:00
-- url     : https://prove2.me/submissions/949eba4d-b18b-47fc-8860-99fae949bb2c

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg
import Theorems.Thm_AaronsonAmbainis_Level_sum_meanAbsIncr_le


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K G : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * G ^ 2 * K ^ 4 * inflR f j ^ 2 := by
  obtain ⟨j, hj⟩ := hI ι f K a ha hsum hrow hvar
  refine ⟨j, le_trans hj ?_⟩
  have hL0 : 0 ≤ ∑ k, meanAbsIncr f k :=
    Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k
  have hL2 : (∑ k, meanAbsIncr f k) ^ 2 ≤ G ^ 2 :=
    pow_le_pow_left₀ hL0 (Level.sum_meanAbsIncr_le f hG) 2
  have hX : 0 ≤ K ^ 4 * inflR f j ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_right hL2 hX
  linarith
end AaronsonAmbainis.Average
