-- Prove2me | Definitions.Def_DeletionCode_FiniteRelationBlocks
-- name    : DeletionCode_FiniteRelationBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:23:42.156082+00:00
-- url     : https://prove2.me/theorems/d07ee1ba-ea6e-4ff7-8e49-fa73c1cf0368
-- title:
--   Finite Relation Blocks
-- statement:
--   Definitions and structural lemmas for Finite Relation Blocks, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteRelationBlocks.lean

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
set_option autoImplicit true
namespace DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
noncomputable def selectedBlocks {k : ℕ} (G I : RuleSet k) : Finset (RuleSet k) := by
  classical
  exact (blocks G).filter (fun B => (B ∩ I).Nonempty)
end DeletionCode.FiniteRelationBlocks


