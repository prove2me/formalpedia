-- Prove2me | Definitions.Def_DeletionCode_CodeExistence
-- name    : DeletionCode_CodeExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:05:43.91817+00:00
-- url     : https://prove2.me/theorems/d17679bd-53f0-4236-b3ab-0270669c3347
-- title:
--   Code Existence
-- statement:
--   Definitions and structural lemmas for Code Existence, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
set_option autoImplicit true
namespace DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection
end DeletionCode.CodeExistence


