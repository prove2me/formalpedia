-- Prove2me | Definitions.Def_DeletionCode_SingleEditBubbles
-- name    : DeletionCode_SingleEditBubbles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:36:28.071514+00:00
-- url     : https://prove2.me/theorems/150ed423-7618-477b-b63c-44e0e2ffc765
-- title:
--   Single Edit Bubbles
-- statement:
--   Definitions and structural lemmas for Single Edit Bubbles, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
namespace DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
namespace LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
def sourceInterval (p : LocalBubble k source target pos orientation) : Set ℕ :=
  Set.Ico p.before.length (p.before.length + p.bubble.negativeWord.length)
end LocalBubble
end DeletionCode.SingleEditBubbles


