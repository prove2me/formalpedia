-- Prove2me | Definitions.Def_ShannonColouring_Shannon
-- name    : ShannonColouring_Shannon
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:52:03.456825+00:00
-- url     : https://prove2.me/theorems/b9ac76a9-6570-44cd-97b9-aca18d24f117
-- title:
--   Shannon
-- statement:
--   Definitions and structural lemmas for Shannon, from Juan Pablo Traverso Gianini (jtraverso/shannon-edge-colouring; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shannon's theorem on edge colourings of multigraphs and its sharpness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean

module
public import Definitions.Def_ShannonColouring_Kempe
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
end ShannonColouring


