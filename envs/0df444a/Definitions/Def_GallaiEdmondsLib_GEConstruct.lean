-- Prove2me | Definitions.Def_GallaiEdmondsLib_GEConstruct
-- name    : GallaiEdmondsLib_GEConstruct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:02:10.851858+00:00
-- url     : https://prove2.me/theorems/7dab8fa5-de84-4344-8d26-8c92df6cf450
-- title:
--   GEConstruct
-- statement:
--   Definitions and structural lemmas for GEConstruct, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
end GallaiEdmonds


