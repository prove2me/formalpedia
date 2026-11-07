-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.explicitBoundPM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:02:09.122196+00:00
-- url     : https://prove2.me/submissions/1adfc881-8ce7-4f64-9229-f1465f51cb6b

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_Bridge_pmt_sqrt_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_Bridge_rpow_five_halves
import Theorems.Thm_AaronsonAmbainis_mainTheorem


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : ExplicitBoundPM := by
  intro n d p hp hbd ε hε hvar
  rw [rpow_five_halves hε.le]
  exact pmt_sqrt_of_mainTheorem AaronsonAmbainis.mainTheorem n d p hp hbd ε hε hvar
end AaronsonAmbainis.Bridge
