-- Prove2me | solution 1 for AaronsonAmbainis.thirdMoment_of_integratedAllPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:44.689216+00:00
-- url     : https://prove2.me/submissions/707f8bec-7dc1-47f5-b63c-f44a1faa50f5

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Theorems.Thm_AaronsonAmbainis_Level_thirdMoment_core

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution :
    IntegratedAllPairsInequality → ThirdMomentInequality := by
  intro hInt ι _ _ f K a ha hsum hrow M hM0 hM s
  have h := Level.thirdMoment_core hInt f a ha hsum hrow hM0 hM s
  have h4 : (4 : ℝ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [div_mul_div_comm, div_le_iff₀ (mul_pos h2 h2)]
  rw [h4] at h
  linarith
end AaronsonAmbainis
