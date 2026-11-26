-- Prove2me | Definitions.Def_HajnalSzemeredi_Main
-- name    : HajnalSzemeredi_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:45:21.899608+00:00
-- url     : https://prove2.me/theorems/cb920d48-4fb8-4d42-9e2f-442552569ffe
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Main.lean

module
public import Definitions.Def_HajnalSzemeredi_Cases
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset Relation
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
end HajnalSzemeredi


