-- Prove2me | solution 1 for AaronsonAmbainis.Level.variance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:04.640418+00:00
-- url     : https://prove2.me/submissions/b7d119f7-baf7-4b90-97c5-71da8beefd10

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) : 0 ≤ variance f := by
  unfold variance
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (by positivity)
end AaronsonAmbainis.Level
