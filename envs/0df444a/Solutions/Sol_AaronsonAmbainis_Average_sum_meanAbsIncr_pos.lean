-- Prove2me | solution 1 for AaronsonAmbainis.Average.sum_meanAbsIncr_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:07.918672+00:00
-- url     : https://prove2.me/submissions/b2e0efb9-7603-4eb2-b3f5-e012e056cb17

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Theorems.Thm_AaronsonAmbainis_Average_exists_meanAbsIncr_pos
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (hMI : MeanIncrementBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    0 < ∑ k, meanAbsIncr f k := by
  obtain ⟨j0, hj0, -⟩ := exists_meanAbsIncr_pos hMI f a ha hsum hrow hvar
  exact lt_of_lt_of_le hj0 (Finset.single_le_sum (f := meanAbsIncr f)
    (fun k _ => Level.meanAbsIncr_nonneg f k) (Finset.mem_univ j0))
end AaronsonAmbainis.Average
