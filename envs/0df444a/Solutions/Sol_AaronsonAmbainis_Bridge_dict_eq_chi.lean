-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.dict_eq_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:09.592706+00:00
-- url     : https://prove2.me/submissions/4266dd72-d0bf-4a05-ab82-1e1d500f3bf2

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) (x : Cube ι) : dict j x = chi {j} x := by
  simp [dict, chi]
end AaronsonAmbainis.Bridge
