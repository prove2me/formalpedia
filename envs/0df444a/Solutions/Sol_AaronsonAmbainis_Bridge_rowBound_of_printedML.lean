-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_of_printedML
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:16.980463+00:00
-- url     : https://prove2.me/submissions/2df2853d-1b6d-4430-a35d-b7c3af297a3e

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBoundFin_of_restricted
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_01
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_fin


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : FbsDegPrintedML) : RowBound :=
  rowBound_of_fin (rowBoundFin_of_restricted
    (fun n d hn hd f hf hdeg => h n d hn hd f hf (hasDegreeLE_iff_01.mp hdeg)))
end AaronsonAmbainis.Bridge
