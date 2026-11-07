-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBoundFin_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:39.53154+00:00
-- url     : https://prove2.me/submissions/cb0ce6b2-04eb-493c-bc74-0d1c061c3c4f

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : RowBound) : RowBoundFin :=
  fun n d f hf hdeg => h (Fin n) d f hf hdeg
end AaronsonAmbainis.Bridge
