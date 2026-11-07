-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.explicitBoundImproved_of_fbsDegreeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:03:27.047807+00:00
-- url     : https://prove2.me/submissions/84ecb461-f9ea-4ab5-8502-01b204176133

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_printed
import Theorems.Thm_AaronsonAmbainis_Bridge_rpow_five_halves
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_sqrt_of_mainTheoremImproved
import Theorems.Thm_AaronsonAmbainis_mainTheoremImproved_of_rowBound


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : FbsDegreeBound → ExplicitBoundImproved := by
  intro h N d p hp hrange ε hε hvar
  rw [rpow_five_halves hε.le]
  exact zo_sqrt_of_mainTheoremImproved
    (AaronsonAmbainis.mainTheoremImproved_of_rowBound (rowBound_of_printed h))
    N d p hp hrange ε hε hvar
end AaronsonAmbainis.Bridge
