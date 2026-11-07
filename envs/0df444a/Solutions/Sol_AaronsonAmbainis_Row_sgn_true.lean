-- Prove2me | solution 1 for AaronsonAmbainis.Row.sgn_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:55:38.781273+00:00
-- url     : https://prove2.me/submissions/9bc9e8be-e567-4cdc-803d-2cca57b75dae

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
namespace AaronsonAmbainis.Row
theorem _root_.solution : sgn true = -1 := by simp [sgn]
end AaronsonAmbainis.Row
