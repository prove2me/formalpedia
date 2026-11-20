-- Prove2me | Definitions.Def_DeletionCode_SupportBlockCount
-- name    : DeletionCode_SupportBlockCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:20:19.542542+00:00
-- url     : https://prove2.me/theorems/a3350c65-8b1a-4610-bc8c-992fc689064e
-- title:
--   Support Block Count
-- statement:
--   Definitions and structural lemmas for Support Block Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
set_option autoImplicit true
namespace DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
end DeletionCode.SupportBlockCount


