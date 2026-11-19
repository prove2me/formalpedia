-- Prove2me | Definitions.Def_DeletionCode_RecordBounds
-- name    : DeletionCode_RecordBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:15:42.581031+00:00
-- url     : https://prove2.me/theorems/02dce979-b9d6-4af9-8cc2-aed15b8deab6
-- title:
--   Record Bounds
-- statement:
--   Definitions and structural lemmas for Record Bounds, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
set_option autoImplicit true
namespace DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
end DeletionCode.RecordBounds


