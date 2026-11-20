-- Prove2me | Definitions.Def_DeletionCode_AttachedBlocks
-- name    : DeletionCode_AttachedBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:17:11.545896+00:00
-- url     : https://prove2.me/theorems/9ce47d1b-8dc9-444f-81f2-8177d52f6dd2
-- title:
--   Attached Blocks
-- statement:
--   Definitions and structural lemmas for Attached Blocks, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
namespace DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators
end DeletionCode.AttachedBlocks


