-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.printed_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:53:55.705827+00:00
-- url     : https://prove2.me/submissions/631fa8d7-7dd0-4a44-b72d-58028051f0bf

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_printedConcl_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_poly_zo


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : RowBound) : FbsDegPrinted :=
  fun n d _ _ f hf hp =>
    (printedConcl_iff f d).mpr (h (Fin n) d f hf (hasDegreeLE_iff_poly_zo.mpr hp))
end AaronsonAmbainis.Bridge
