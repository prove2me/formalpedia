-- Prove2me | solution 1 for AaronsonAmbainis.Average.influence_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:49.960655+00:00
-- url     : https://prove2.me/submissions/3ae9336e-dc5e-4440-92b5-3977d957901b

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Theorems.Thm_AaronsonAmbainis_Average_influence_of_incr
import Theorems.Thm_AaronsonAmbainis_Level_sum_abs_incr_le_of_rows


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * K ^ 6 * inflR f j ^ 2 := by
  obtain ⟨j, hj⟩ := influence_of_incr hI f a ha hsum hrow
    (Level.sum_abs_incr_le_of_rows hsum hrow) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring
end AaronsonAmbainis.Average
