-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_meanAbsIncr_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:34.218217+00:00
-- url     : https://prove2.me/submissions/92bfebc5-9ec3-40ea-b233-428bd32d4ee1

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_sum_abs_incr_le_of_rows
import Theorems.Thm_AaronsonAmbainis_Level_sum_meanAbsIncr_le

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) :
    ∑ j, meanAbsIncr f j ≤ K :=
  sum_meanAbsIncr_le f (sum_abs_incr_le_of_rows hsum hrow)
end AaronsonAmbainis.Level
