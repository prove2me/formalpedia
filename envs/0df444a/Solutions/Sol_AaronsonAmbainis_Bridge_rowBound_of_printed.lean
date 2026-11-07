-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_of_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:53:55.201537+00:00
-- url     : https://prove2.me/submissions/0282a9c5-b588-46a3-bdcd-c1bdf41ddde1

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBoundFin_of_restricted
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_poly_zo
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_fin


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : FbsDegPrinted) : RowBound :=
  rowBound_of_fin (rowBoundFin_of_restricted
    (fun n d hn hd f hf hdeg => h n d hn hd f hf (hasDegreeLE_iff_poly_zo.mp hdeg)))
end AaronsonAmbainis.Bridge
