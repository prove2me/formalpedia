-- Prove2me | solution 1 for AaronsonAmbainis.Average.flipSet_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:35:58.391204+00:00
-- url     : https://prove2.me/submissions/5c291b62-8a04-4e0d-b71b-64cd1e8ceb38

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (x : Cube ι) (S T : Finset ι) :
    flipSet (flipSet x S) T = flipSet (flipSet x T) S := by
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [flipSet, hS, hT]
end AaronsonAmbainis.Average
