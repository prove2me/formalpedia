-- Prove2me | Definitions.Def_HajnalSzemeredi_Cases
-- name    : HajnalSzemeredi_Cases
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:44:51.524653+00:00
-- url     : https://prove2.me/theorems/bf0c23c3-95e8-569b-b1a9-cacdef023832
-- title:
--   Cases
-- statement:
--   Definitions and structural lemmas for Cases, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Cases.lean

module
public import Definitions.Def_HajnalSzemeredi_Shift
public import Definitions.Def_HajnalSzemeredi_Structure
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset Relation
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
end HajnalSzemeredi


