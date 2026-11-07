-- Prove2me | solution 1 for AaronsonAmbainis.Level.exists_meanAbsIncr_ge_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:38.910125+00:00
-- url     : https://prove2.me/submissions/ea8f84a6-c943-4be6-81c7-1429cacf2cbe

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Theorems.Thm_AaronsonAmbainis_Level_cube_le_iff_mul_sqrt_le
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hMI : MeanIncrementBound) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (hvar : 0 < variance f) :
    ∃ j, variance f * Real.sqrt (variance f) ≤ 6 * K ^ 2 * meanAbsIncr f j := by
  obtain ⟨j, hj⟩ := hMI ι f K a ha hsum hrow hvar
  exact ⟨j, (cube_le_iff_mul_sqrt_le hvar.le (meanAbsIncr_nonneg f j)).mp hj⟩
end AaronsonAmbainis.Level
