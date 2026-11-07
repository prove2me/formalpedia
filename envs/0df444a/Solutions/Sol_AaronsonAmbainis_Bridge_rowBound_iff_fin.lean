-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_iff_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:33:36.330517+00:00
-- url     : https://prove2.me/submissions/9962eb43-bbea-45ca-bb36-ce8f45863907

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_fin
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBoundFin_of_rowBound

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : RowBound ↔ RowBoundFin :=
  ⟨rowBoundFin_of_rowBound, rowBound_of_fin⟩
end AaronsonAmbainis.Bridge
