-- Prove2me | Definitions.Def_DeletionCode_LocalBubbleDisjoint
-- name    : DeletionCode_LocalBubbleDisjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:41:54.733266+00:00
-- url     : https://prove2.me/theorems/e6d8cb71-626a-4ad3-8453-6b3a0ef95469
-- title:
--   Local Bubble Disjoint
-- statement:
--   Definitions and structural lemmas for Local Bubble Disjoint, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
set_option autoImplicit true
namespace DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
def pathWord (p : LocalBubble k source target pos orientation) (side : Bool) : List Bool :=
  if side then p.bubble.positiveWord else p.bubble.negativeWord
def canonicalEdit (p : LocalBubble k source target pos orientation) : Bool → Edit
  | false => .unchanged
  | true => match p.bubble.orientation with
    | .deletion => .delete (p.before.length + editOffset k)
    | .insertion => .insert (p.before.length + editOffset k) p.bubble.bit
def localVertex (p : LocalBubble k source target pos orientation) (side : Bool)
    (offset : ℕ) : SupportComponents.Vertex (windowLength k) :=
  SpectrumPath.vertexAt (listLetters (pathWord p side)) (windowLength k) offset
def vertices (p : LocalBubble k source target pos orientation) (side : Bool) :
    Set (SupportComponents.Vertex (windowLength k)) :=
  {v | ∃ offset, offset + (windowLength k - 1) ≤ (pathWord p side).length ∧
    localVertex p side offset = v}
end DeletionCode.LocalBubbleDisjoint


