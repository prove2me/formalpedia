-- Prove2me | Definitions.Def_DeletionCode_EditRigidity
-- name    : DeletionCode_EditRigidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:19:09.666323+00:00
-- url     : https://prove2.me/theorems/e0aa8245-06e7-47c2-b814-0795572b04ee
-- title:
--   Edit Rigidity
-- statement:
--   Definitions and structural lemmas for Edit Rigidity, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
namespace DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins
end DeletionCode.EditRigidity


