-- Prove2me | Definitions.Def_DeletionCode_BlockAdjunction
-- name    : DeletionCode_BlockAdjunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:20:17.162435+00:00
-- url     : https://prove2.me/theorems/b495ff21-2b3f-4625-86eb-9c9994106624
-- title:
--   Block Adjunction
-- statement:
--   Definitions and structural lemmas for Block Adjunction, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
set_option autoImplicit true
namespace DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
end DeletionCode.BlockAdjunction


