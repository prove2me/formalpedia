-- Prove2me | solution 1 for AaronsonAmbainis.diffSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:34.541396+00:00
-- url     : https://prove2.me/submissions/5dbb1b5b-7f6c-43b3-8c70-8cfd06e49200

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]
end AaronsonAmbainis
