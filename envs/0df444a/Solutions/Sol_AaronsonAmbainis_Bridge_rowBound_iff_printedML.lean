-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_iff_printedML
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:33:58.737658+00:00
-- url     : https://prove2.me/submissions/94815bdd-397b-48c1-b99d-df71330ff968

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_printedML
import Theorems.Thm_AaronsonAmbainis_Bridge_printedML_of_rowBound

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : RowBound ↔ FbsDegPrintedML :=
  ⟨printedML_of_rowBound, rowBound_of_printedML⟩
end AaronsonAmbainis.Bridge
