-- Prove2me | Definitions.Def_HajnalSzemeredi_Shift
-- name    : HajnalSzemeredi_Shift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:44:00.518808+00:00
-- url     : https://prove2.me/theorems/c6175d16-65b5-5bdf-aad5-c1b0c76c2054
-- title:
--   Shift
-- statement:
--   Definitions and structural lemmas for Shift, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Shift.lean

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Definitions.Def_HajnalSzemeredi_Reach
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset Relation
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
end HajnalSzemeredi


