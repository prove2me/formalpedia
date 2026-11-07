-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mainBound_of_mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:16:39.612196+00:00
-- url     : https://prove2.me/submissions/41ff9965-e351-4f33-8a40-b709f753df18

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : MainTheorem) : MainBound (50000 * Real.pi ^ 8) := h
end AaronsonAmbainis.Bridge
