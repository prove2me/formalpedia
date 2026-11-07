-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.printedML_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:07.131198+00:00
-- url     : https://prove2.me/submissions/1fd7aebc-be2b-4f1d-8fd0-bda56367dd01

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_printedConcl_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_01


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : RowBound) : FbsDegPrintedML :=
  fun n d _ _ f hf hp =>
    (printedConcl_iff f d).mpr (h (Fin n) d f hf (hasDegreeLE_iff_01.mpr hp))
end AaronsonAmbainis.Bridge
