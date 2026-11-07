-- Prove2me | solution 1 for AaronsonAmbainis.Level.meanAbsIncr_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:07.261334+00:00
-- url     : https://prove2.me/submissions/0fb6d011-f1c8-49fe-807a-0c04f1f5cf94

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (j : ι) : 0 ≤ meanAbsIncr f j :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
end AaronsonAmbainis.Level
