-- Prove2me | Definitions.Def_DeletionCode_LargeBlockSelection
-- name    : DeletionCode_LargeBlockSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:20:50.419759+00:00
-- url     : https://prove2.me/theorems/0ca07129-edcd-42d3-a154-b201239a9d8a
-- title:
--   Large Block Selection
-- statement:
--   Definitions and structural lemmas for Large Block Selection, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean

import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
namespace DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction
end DeletionCode.LargeBlockSelection


