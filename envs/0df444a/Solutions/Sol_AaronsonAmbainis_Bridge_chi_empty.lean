-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.chi_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:15.870533+00:00
-- url     : https://prove2.me/submissions/67276dee-1917-48e1-a31a-0baabec56f0f

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) : chi (∅ : Finset ι) x = 1 := by
  simp [chi]
end AaronsonAmbainis.Bridge
