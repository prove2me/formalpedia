-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mainBound_of_mainTheoremImproved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:29.78929+00:00
-- url     : https://prove2.me/submissions/94545829-9bcf-4bfe-a474-20d3be84f263

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheoremImproved) :
    MainBound (3125 * Real.pi ^ 8) := h
end AaronsonAmbainis.Bridge
