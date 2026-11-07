-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_antipode_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:25.456076+00:00
-- url     : https://prove2.me/submissions/1fbe4078-caaf-4e6c-9504-c6d0f80cc539

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (u : Cube ι) (A : Finset ι) :
    flipSet (antipode u) (univ \ A) = flipSet u A := by
  funext i
  by_cases h : i ∈ A <;> simp [flipSet, antipode, h]
end AaronsonAmbainis.Bridge
