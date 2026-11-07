-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.explicitBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:59:43.736292+00:00
-- url     : https://prove2.me/submissions/2725c00e-b23c-4946-95b8-6522cd9249f3

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_Bridge_rpow_five_halves
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_sqrt_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_mainTheorem


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : ExplicitBound := by
  intro N d p hp hrange ε hε hvar
  rw [rpow_five_halves hε.le]
  exact zo_sqrt_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar
end AaronsonAmbainis.Bridge
