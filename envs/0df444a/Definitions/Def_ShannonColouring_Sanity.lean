-- Prove2me | Definitions.Def_ShannonColouring_Sanity
-- name    : ShannonColouring_Sanity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:02:57.587203+00:00
-- url     : https://prove2.me/theorems/4aaf908f-6566-4a87-89bd-f4523ddf02d7
-- title:
--   Sanity
-- statement:
--   Definitions and structural lemmas for Sanity, from Juan Pablo Traverso Gianini (jtraverso/shannon-edge-colouring; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shannon's theorem on edge colourings of multigraphs and its sharpness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ShannonColouring
def singleEdge : Unit → Fin 2 × Fin 2 := fun _ => (0, 1)
def triangle : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (1, 2), (0, 2)]
end ShannonColouring


