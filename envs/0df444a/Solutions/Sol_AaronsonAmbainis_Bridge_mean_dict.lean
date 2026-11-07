-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mean_dict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:30.829225+00:00
-- url     : https://prove2.me/submissions/652eff2c-3743-418c-8fad-a718e2487d9c

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_sum_dict

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) : mean (dict j) = 0 := by
  simp [mean, sum_dict]
end AaronsonAmbainis.Bridge
