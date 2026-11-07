-- Prove2me | solution 1 for AaronsonAmbainis.Level.variance_eq_zero_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:05.20485+00:00
-- url     : https://prove2.me/submissions/4caf6319-832a-4baf-9c29-53dd3939dec7

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_const

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution [IsEmpty ι] (f : Cube ι → ℝ) : variance f = 0 :=
  variance_eq_zero_of_const f (fun x y => congrArg f (Subsingleton.elim x y))
end AaronsonAmbainis.Level
