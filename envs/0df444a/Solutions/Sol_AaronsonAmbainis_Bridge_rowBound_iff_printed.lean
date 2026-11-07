-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:56:27.124296+00:00
-- url     : https://prove2.me/submissions/17bdf9d1-780a-4e9d-bdc6-f294dd4e54a3

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_printed
import Theorems.Thm_AaronsonAmbainis_Bridge_printed_of_rowBound

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : RowBound ↔ FbsDegPrinted :=
  ⟨printed_of_rowBound, rowBound_of_printed⟩
end AaronsonAmbainis.Bridge
