-- Prove2me | solution 1 for AaronsonAmbainis.meanIncrement_of_thirdMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:39.762609+00:00
-- url     : https://prove2.me/submissions/636aa7b8-9497-4d20-810f-73d56e93b9b5

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Theorems.Thm_AaronsonAmbainis_Level_variance_cube_le
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg
import Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_isEmpty


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : ThirdMomentInequality → MeanIncrementBound := by
  intro hTM ι _ _ f K a ha hsum hrow hvar
  have hne : Nonempty ι := by
    by_contra hemp
    have hι : IsEmpty ι := not_nonempty_iff.mp hemp
    rw [Level.variance_eq_zero_of_isEmpty f] at hvar
    exact lt_irrefl 0 hvar
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ (meanAbsIncr f) univ_nonempty
  exact ⟨j, Level.variance_cube_le hTM f a ha hsum hrow (Level.meanAbsIncr_nonneg f j)
    (fun j' => hj j' (mem_univ _))⟩
end AaronsonAmbainis
