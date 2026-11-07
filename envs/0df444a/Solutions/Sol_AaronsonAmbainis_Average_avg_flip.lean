-- Prove2me | solution 1 for AaronsonAmbainis.Average.avg_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:14.174271+00:00
-- url     : https://prove2.me/submissions/5053fb8c-fdb5-4137-88bc-91585b7970c7

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_flipSet_flipSet_self


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j : ι) (f : Cube ι → ℝ) (x : Cube ι) : avg j f (flipSet x {j}) = avg j f x := by
  unfold avg
  rw [flipSet_flipSet_self]
  ring
end AaronsonAmbainis.Average
