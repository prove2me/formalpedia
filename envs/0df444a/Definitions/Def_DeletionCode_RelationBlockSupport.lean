-- Prove2me | Definitions.Def_DeletionCode_RelationBlockSupport
-- name    : DeletionCode_RelationBlockSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:09:04.360178+00:00
-- url     : https://prove2.me/theorems/8289b2ef-a9cb-4ed6-8f6a-aff827ebc88f
-- title:
--   Relation Block Support
-- statement:
--   Definitions and structural lemmas for Relation Block Support, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean

import Definitions.Def_DeletionCode_RelationSupport
set_option autoImplicit true
namespace DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
end DeletionCode.RelationBlockSupport


