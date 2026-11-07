-- Prove2me | solution 1 for AaronsonAmbainis.Level.inflR_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:33.836146+00:00
-- url     : https://prove2.me/submissions/7bb962f4-ea26-490b-8f2b-c17eb54953e9

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (j : ι) : 0 ≤ inflR f j := by
  unfold inflR
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (by positivity)
end AaronsonAmbainis.Level
