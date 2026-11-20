-- Prove2me | Definitions.Def_DeletionCode_BubbleCatalogue
-- name    : DeletionCode_BubbleCatalogue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:19:37.645572+00:00
-- url     : https://prove2.me/theorems/94d29032-5ef4-4b3a-beda-3ee56f6712fd
-- title:
--   Bubble Catalogue
-- statement:
--   Definitions and structural lemmas for Bubble Catalogue, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
set_option autoImplicit true
namespace DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
def pathWord {k : ℕ} (bubble : BubbleWord k) (side : Bool) : List Bool :=
  if side then bubble.positiveWord else bubble.negativeWord
end DeletionCode.BubbleCatalogue


